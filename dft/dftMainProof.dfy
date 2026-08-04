lemma setcardinality(n: int)
    requires n >= 0
    ensures |set x| 0 <= x < n| == n 

{
    if n == 0 { 
        assert (set x| 0 <= x < n) == {};
    }
    else {
        setcardinality(n - 1);
        assert (set x| 0 <= x < n) == (set x| 0 <= x < n - 1) + {n - 1}; 
    } 
}

lemma subsetcardinality(a: set<int>, b: set<int>)
    requires a <= b
    ensures |a| <= |b|
{
    if a == {} {
        assert |a| == 0;
        assert a <= b;
    } else {
        var x :| x in a;
        subsetcardinality(a - {x}, b - {x});
    }
}

predicate fringeable(adj: array2<bool>, u: int, v: int, visited: set<int>)
    reads adj
    requires adj.Length0 == adj.Length1
    requires 0 <= u < adj.Length0
    requires 0 <= v < adj.Length1
    requires visited <= set x | 0 <= x < adj.Length0 // We want to make the visited set, a portion of vertices of the graph. That portion is named Fringe
    requires 0 <= |visited| <= adj.Length0
    decreases adj.Length0 - |visited|


{
    if u in visited then
        false 
    else if u == v then
        true
    else 
    setcardinality(adj.Length0);
    assert u !in visited;
    assert u in (set x | 0 <= x < adj.Length0);
    assert visited + {u} <= (set x | 0 <= x < adj.Length0); //in order to assert this, we need a lemma that tells dafny how to calculate it 
    subsetcardinality(visited + {u}, set x | 0 <= x < adj.Length0);
    assert |visited + {u}| == |visited| + 1; // the same here, dafny doesnt now this by standard, we need to show how
    assert |visited + {u}| <= adj.Length0;   
    assert |visited| < adj.Length0;           

    // with the lemmas and asserts, we prove the pre-condition, and finally guarantee the post-condition

    exists w :: 0 <= w < adj.Length0 && adj[u,w] && fringeable(adj, w, v, visited + {u})
     
}





method depthFirstTreaversal()

{
    //TODO: 
}