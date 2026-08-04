lemma cardinality(n: int)
    requires n >= 0
    ensures |set x| 0 <= x < n| == n 

{
    if n == 0 { 
        assert (set x| 0 <= x < n) == {};
    }
    else {
        cardinality(n - 1);
        assert (set x| 0 <= x < n) == (set x| 0 <= x < n - 1) + {n - 1}; 
    } 
}

predicate fringeable(adj: array2<bool>, u: int, v: int, visited: set<int>)
    reads adj
    requires adj.Length0 == adj.Length1
    requires 0 <= u < adj.Length0
    requires 0 <= v < adj.Length1
    requires visited <= set x | 0 <= x < adj.Length0 // We want that the visited set, is a portion of the vertices on the graph. The same portion that fits the DFT method. That portion is named Fringe
    requires 0 <= |visited| <= adj.Length0
    decreases adj.Length0 - |visited|


{
    if u in visited then
        false 
    else if u == v then
        true
    else 
        cardinality(adj.Length0);
        cardinality(adj.Length1);
        assert u !in visited;
        assert  visited < (set x | 0 <= x < adj.Length0);
        assert |visited| <= adj.Length0;
        assert |visited + {u}| == |visited| + 1;
        exists w :: 0 <= w < adj.Length0 && adj[u,w] && fringeable(adj, w, v, visited + {u})
     
}



method depthFirstTreaversal()

{
    //TODO: invariantes, gestao da orla
}