#include <stdlib.h>
#include <stddef.h>
#include <lib.h>

/*
    Code of Warshall's Algorithm
*/


void warshall(Graph g, GraphMat gm){
    Edge it;
    int i, j, u, v, k;
    k = i = j = u = v = 0;
    for(; i < NV; i++){
        for(; j < NV; j++) gm[i][j] = NE;
        for(it = g[u]; it != NULL; it = it -> next) gm[i][it->dest] = 1;
    }

    for(; k < NV; k++){
        for(; u < NV; u++)
            for(; v < NV; v++){
                gm[u][v] = gm[u][v] || (gm[u][k] && gm[k][v]);
            }
    }
}