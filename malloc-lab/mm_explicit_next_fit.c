/*
 * 명시적 가용 리스트의 next-fit 할당기.
 * 가용 블록은 등록 순서로 연결하며, 검색 실패 시 지연 병합한다.
 * 힙 끝의 가용 공간이 있으면 부족한 크기만 확장한다.
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
static void *last_free_bp; /* 가용 리스트 맨 앞: 가장 먼저 등록된 블록 */
static void *free_tail_bp; /* 가용 리스트 맨 뒤: 가장 최근 등록된 블록 */
static void *next_fit_bp; /* 다음 검색을 시작할 가용 노드 */

static void *coalesce(void *dp);
static void integrate_heap(void);
static void *extend_heap(size_t words);

typedef struct free_ptr {
  long long *p_prev; /* 리스트의 이전 노드 포인터: 더 먼저 등록된 블록 */
  long long *p_next; /* 리스트의 다음 노드 포인터: 더 최근 등록된 블록 */
} free_ptr_t;

/*
 * 리스트에 없는 free 블록을 맨 뒤에 등록 (FIFO).
 * 꼬리 포인터로 탐색 없이 삽입하고, 할당은 next-fit 위치부터 검색.
 * 헤더/푸터는 호출하는 함수에서 설정하며, 링크는 payload에 저장.
 */
static void insert_free(void *bp) {
  GET_FREE_PTR(bp)->p_prev = free_tail_bp;
  GET_FREE_PTR(bp)->p_next = NULL;
  if (free_tail_bp != NULL) {
    GET_FREE_PTR(free_tail_bp)->p_next = bp;
  } else {
    last_free_bp = bp;
  }
  free_tail_bp = bp;
  if (next_fit_bp == NULL) {
    next_fit_bp = bp;
  }
}

/*
 * 리스트에 등록된 free 블록 삭제: prev -> bp -> next를 prev -> next로 연결.
 * 첫 노드이면 시작점을 갱신, 이웃이 있을 때만 해당 필드에 접근.
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
  } else {
    free_tail_bp = prev;
  }
  /* 할당·병합으로 검색 노드가 사라지면 다음 노드로 이동하고 끝에서 순환. */
  if (next_fit_bp == bp) {
    next_fit_bp = next != NULL ? (void *)next : last_free_bp;
  }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  last_free_bp = NULL;
  free_tail_bp = NULL;
  next_fit_bp = NULL;
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

  /* 확장 직전 전체 병합을 마쳤으므로, 남아 있는 이전 가용 블록만 연결. */
  return coalesce(bp);
}

static void *find_fit(size_t size) {
  /* 마지막 선택 위치부터 이어서 검색하며, 가용 리스트를 한 바퀴만 검사. */
  void *start = next_fit_bp;
  if (start == NULL) {
    return NULL;
  }

  void *bp = start;
  do {
    if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= size) {
      next_fit_bp = bp; /* place()의 remove_free()가 다음 검색 위치를 갱신. */
      return bp;
    }
    bp = GET_FREE_PTR(bp)->p_next;
    if (bp == NULL) {
      bp = last_free_bp;
    }
  } while (bp != start);

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

  /* 검색 실패 시에만 병합하고 재검색: 가능한 기존 공간부터 재사용. */
  integrate_heap();
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* 병합 후에도 찾지 못하면 더 큰 메모리를 확보하고 블록 배치. */
  extend_size = MAX(asize, CHUNKSIZE);
  /* 에필로그의 블록 포인터는 힙 마지막 바이트 바로 다음 주소. */
  char *tail_bp = PREV_BLXP((char *)mem_heap_hi() + 1);
  if (!GET_ALLOC(HDRP(tail_bp))) {
    /* 힙 끝의 가용 공간과 즉시 병합하므로 부족한 부분만 추가 */
    extend_size = asize - GET_SIZE(HDRP(tail_bp));
  }
  if ((bp = extend_heap(extend_size / WSIZE)) == NULL) {
    return NULL;
  }
  place(bp, asize);
  return bp;
}

/*
 * mm_free - 병합은 미루고 가용 리스트에 등록.
 */
void mm_free(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  insert_free(bp);
}

/*
 * 물리적 힙 순서로 연속된 가용 블록을 한 번에 병합.
 * 단독 가용 블록은 그대로 두어 등록 순서를 유지하고,
 * 병합할 블록만 리스트에서 제거한 뒤 결과를 맨 뒤에 한 번 등록.
 */
static void integrate_heap(void) {
  char *bp = NEXT_BLXP(heap_listp);

  while (GET_SIZE(HDRP(bp)) != 0) {
    char *next = NEXT_BLXP(bp);
    if (GET_ALLOC(HDRP(bp)) || GET_ALLOC(HDRP(next))) {
      bp = next;
      continue;
    }

    size_t size = GET_SIZE(HDRP(bp));
    remove_free(bp); /* bp도 free 시 이미 등록됐으므로 먼저 제거. */
    do {
      size += GET_SIZE(HDRP(next));
      remove_free(next);
      next = NEXT_BLXP(next); /* 원래 헤더가 남아 있을 때 다음 주소 계산. */
    } while (!GET_ALLOC(HDRP(next)));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_free(bp);
    bp = next; /* 병합에 포함된 내부 헤더들은 건너뜀. */
  }
}

/*
 * coalesce - 힙 확장 시 새 블록을 기존 가용 블록과 연결.
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
  copySize = *(size_t *)((char *)oldptr - WSIZE);
  if (size < copySize)
    copySize = size;
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}
