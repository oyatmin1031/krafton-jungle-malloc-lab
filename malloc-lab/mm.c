/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Krafton Jungle SW-AI",
    /* First member's full name */
    "Minho Lee",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             /* Word size (byte) */
#define DSIZE 8             /* Double word size (byte) */
#define CHUNKSIZE (1<<12)   /* 힙 확장 크기(byte) */

#define MAX(x, y)   ((x) > (y) ? (x) : (y))

/* size와 allocated field 비트 결합 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p의 워드 읽고, 쓰기*/
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

/* 주소 p의 size와 allocated field 비트 가져오기*/
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* 블록 포인터 bp를 통해 header와 footer 주소 계산 */
#define HDRP(bp)        ((char*)(bp) - WSIZE)
#define FTRP(bp)        ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp를 통해 이전과 다음 블록 주소 게산 */
#define NEXT_BLXP(bp)   ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLXP(bp)   ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))


static char* heap_listp;

static void* coalesce(void* dp);
static void* extend_heap(size_t words);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 빈 초기 힙 생성 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
        return -1;
    }

    PUT(heap_listp, 0);                             /* 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 헤더 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 푸터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* 에필로그 헤더 */
    heap_listp += (2*WSIZE);

    /* CHUNKSIZE byte의 free block으로 빈 힙 확장 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/* 새 가용 블록으로 힙 확장 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* 정렬 유지를 위해 짝수 워드 만큼의 공간 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    /* free block의 header와 footer, epilogue header 초기화 */
    PUT(HDRP(bp), PACK(size, 0));           /* free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* free block footer */
    PUT(HDRP(NEXT_BLXP(bp)), PACK(0, 1));   /* 새 에필로그 헤더 */

    /* 이전 블록이 free라면 연결 */
    return coalesce(bp);
}

static void* find_fit(size_t size) {
    /* 첫 위치부터 헤더를 보고 맞는 사이즈의 블록을 찾아 이동 후 포인터 반환 */
    void* bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLXP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= size) {
            return bp;
        } 
    }
    return NULL;
}

static void place(char* bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLXP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* 조정된 블록 사이즈 */
    size_t extendsize;  /* */
    char* bp;

    /* size가 0인 요청 무시 */
    if (size == 0) {
        return NULL;
    }

    /* 블록 사이즈 조정 */
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    /* 맞는 free block 검색 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 찾지 못했을 때. 더 큰 메모리를 확보하고 블록 배치 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* 
 * coalesce - free block 연결
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLXP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLXP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLXP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLXP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLXP(bp)), PACK(size, 0));
        bp = PREV_BLXP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLXP(bp))) + GET_SIZE(FTRP(NEXT_BLXP(bp)));
        PUT(HDRP(PREV_BLXP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLXP(bp)), PACK(size, 0));
        bp = PREV_BLXP(bp);
    }

    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

