#include <stdlib.h>
#include <stddef.h>

#define NV 7
#define NE 0 // weight of the non-linked edge

typedef struct edge{ 
    int cost;
    int dest;
    struct edge *next;
} *Edge;

typedef int GraphMat [NV][NV];

typedef Edge Graph [NV];