#include <stdlib.h>
#include <stddef.h>

#define NV 7
#define NE 0

typedef struct edge{ 
    int cost;
    int dest;
    struct edge *next;
} *Edge;

typedef int GraphMat [NV][NV];

typedef Edge Graph [NV];

/*
    Code of Warshall's Algorithm
*/


void warshall(Graph g, GraphMat gm){
    Edge it;
    int i, j, u, v, k;
    i = j = u = v = 0;
    for(; i < NV; i++){
        for(; j < NV; j++) gm[i][j] = NE;
        for(it = g[u]; it != NULL; it = it -> next) gm[i][it->dest] = 1;
    }

    for(k = 0; k < NV; k++){
        for(; u < NV; u++)
            for(; v < NV; v++){
                gm[u][v] = gm[u][v] || (gm[u][k] && gm[k][v]);
            }
    }
}