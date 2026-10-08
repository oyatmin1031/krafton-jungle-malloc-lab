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
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

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
#define CHUNKSIZE (1 << 12) /* 힙 확장 크기(byte) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* size와 allocated field 비트 결합 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p의 워드 읽고, 쓰기*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p의 size와 allocated field 비트 가져오기*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define GET_FREE_PTR(p) ((struct free_ptr *)(p))

/* 블록 포인터 bp를 통해 header와 footer 주소 계산 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp를 통해 이전과 다음 블록 주소 게산 */
#define NEXT_BLXP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLXP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;
static void *last_free_bp; /* 가용 리스트 맨 앞: 가장 최근 등록된 블록 */

static void *coalesce(void *dp);
static void *extend_heap(size_t words);

typedef struct free_ptr {
  long long *p_prev; /* 리스트의 이전 노드: 더 최근 등록된 블록 */
  long long *p_next; /* 리스트의 다음 노드: 더 먼저 등록된 블록 */
} free_ptr_t;

/*
 * 리스트에 없는 free 블록을 맨 앞에 등록 (LIFO).
 * bp와 기존 첫 노드의 양방향 링크를 연결한 뒤 시작점을 갱신.
 * 헤더/푸터는 호출하는 함수에서 설정하며, 링크는 payload에 저장.
 */
static void insert_free(void *bp) {
  GET_FREE_PTR(bp)->p_prev = NULL;
  GET_FREE_PTR(bp)->p_next = last_free_bp;
  if (last_free_bp != NULL) {
    GET_FREE_PTR(last_free_bp)->p_prev = bp;
  }
  last_free_bp = bp;
}

/*
 * 리스트에 등록된 free 블록을 삭제: prev -> bp -> next를 prev -> next로 연결.
 * 첫 노드이면 시작점을 갱신하고, 이웃이 있을 때만 해당 필드에 접근.
 * 유일한 노드를 삭제하면 last_free_bp가 NULL이 됨.
 */
static void remove_free(void *bp) {
  long long *prev = GET_FREE_PTR(bp)->p_prev;
  long long *next = GET_FREE_PTR(bp)->p_next;

  if (prev != NULL) {
    GET_FREE_PTR(prev)->p_next = next;
  } else {
    last_free_bp = next;
  }
  if (next != NULL) {
    GET_FREE_PTR(next)->p_prev = prev;
  }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  last_free_bp = NULL;
  /* 빈 초기 힙 생성 */
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
    return -1;
  }

  PUT(heap_listp, 0);                            /* 패딩 */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더 */
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* 프롤로그 푸터 */
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* 에필로그 헤더 */
  heap_listp += (2 * WSIZE);

  /* CHUNKSIZE byte의 free block으로 빈 힙 확장 */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
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
  PUT(HDRP(bp), PACK(size, 0));         /* free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
  PUT(HDRP(NEXT_BLXP(bp)), PACK(0, 1)); /* 새 에필로그 헤더 */

  /* 이전 블록이 free라면 연결 */
  return coalesce(bp);
}

static void *find_fit(size_t size) {
  /* 첫 위치부터 헤더를 보고 맞는 사이즈의 블록을 찾아 이동 후 포인터 반환 */
  void *bp = last_free_bp;
  if (bp == NULL) {
    return NULL;
  }

  do {
    if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= size) {
      return bp;
    }
    bp = GET_FREE_PTR(bp)->p_next;
  } while (bp != NULL);

  return NULL;
}

static void place(char *bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));
  /* 할당 전에 리스트에서 제거: 이후 payload는 사용자 데이터가 됨. */
  remove_free(bp);

  if ((csize - asize) >= (3 * DSIZE)) {
    /* 헤더 할당 */
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));

    /* 남은 부분 free 블록으로 */
    bp = NEXT_BLXP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));

    /* 분할한 나머지만 다시 free 노드로 등록. */
    insert_free(bp);
  } else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
  size_t asize;       /* 조정된 블록 사이즈 */
  size_t extend_size; /* 확장할 사이즈 */
  char *bp;

  /* size가 0인 요청 무시 */
  if (size == 0) {
    return NULL;
  }

  /* 블록 사이즈 조정 - 기본 24byte */
  if (size <= 2 * DSIZE) {
    asize = 3 * DSIZE;
  } else {
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  /* 맞는 free block 검색 */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* 찾지 못했을 때. 더 큰 메모리를 확보하고 블록 배치 */
  extend_size = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extend_size / WSIZE)) == NULL) {
    return NULL;
  }
  place(bp, asize);
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
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

  /* bp는 아직 리스트에 없음. 병합할 이웃만 먼저 삭제하고 결과를 등록. */
  if (prev_alloc && next_alloc) {
    insert_free(bp);
    return bp;
  }

  /* 이전 블록은 할당, 다음 블록은 가용 */
  else if (prev_alloc && !next_alloc) {
    remove_free(NEXT_BLXP(bp));

    size += GET_SIZE(HDRP(NEXT_BLXP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    insert_free(bp);
  }

  /* 이전 블록은 가용, 다음 블록은 할당 */
  else if (!prev_alloc && next_alloc) {
    remove_free(PREV_BLXP(bp));

    size += GET_SIZE(HDRP(PREV_BLXP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLXP(bp)), PACK(size, 0));
    bp = PREV_BLXP(bp);

    insert_free(bp);
  }

  /* 이전 블록 가용, 다음 블록 가용 */
  else {
    /* 리스트 순서는 물리적 블록 순서와 다름. 각 삭제 시 현재 링크를 읽음. */
    remove_free(PREV_BLXP(bp));
    remove_free(NEXT_BLXP(bp));

    size += GET_SIZE(HDRP(PREV_BLXP(bp))) + GET_SIZE(FTRP(NEXT_BLXP(bp)));
    PUT(HDRP(PREV_BLXP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLXP(bp)), PACK(size, 0));
    bp = PREV_BLXP(bp);

    insert_free(bp);
  }

  return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
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
