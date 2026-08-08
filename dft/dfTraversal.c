#include <stdlib.h>
#include <stddef.h>
#include <lib.h>

int dfRec(Graph g, int origin, int v[]){
    int count = 1;
    Edge it; 
    v[origin] = 1;
    for(it = g[origin]; it !=  NULL; it = it -> next)
        if(!v[it->dest])
            count += dfRec(g, it -> dest, v);
    return count;
}

int dftraversal(Graph g, int origin){
    int visited[NV]; int i;
    for(i = 0; i < NV; i++) visited[i] = 0;
    return dfRec(g, origin, visited);
}