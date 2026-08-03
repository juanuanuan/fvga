/* The calculation of a non-oriented non-connected/(connected) graph by Warshall's Algorithm is based on iterating over all vertices (V):
    
    
    It = {}
    G+ = G ∪ { (u,v) | (u,x) ∈ G+ ∧ (x,v) ∈ G+ }
    while (It != V)
        let x ∈ V - It
        G+ = G ∪ { (u,v) | (u,x) ∈ G+ ∧ (x,v) ∈ G+ }
        It := It U {x}

    An invariant for this cicle could be: 
       I = In each cicle's iteration (It), the G+ graph contains information about the paths in G. Those same paths use the vertices in It as intermediary nodes.
    
    The fact is, as It is initially empty, there only exists an edge in G+ if and only if there is an edge in G.
    
    
    The correctness of Warshall's algorithm does not depend on the order in which
    vertices are added to It — only on which set of vertices has been processed so
    far.

    This Dafny implementation only verifies one fixed order (0, 1, ..., n-1, via the
    k < n loop).


*/


predicate existsPath(adj: array2<bool>, u: int, v: int, k: int)
    reads adj
    requires adj.Length0 == adj.Length1
    requires 0 <= u < adj.Length0
    requires 0 <= v < adj.Length1
    requires 0 <= k <= adj.Length0
    decreases k
{
    if k == 0 then 
        u == v || adj[u, v]
    else 
        existsPath(adj, u, v, k - 1) || (existsPath(adj, u, k - 1, k - 1) && existsPath(adj, k - 1, v, k - 1))
}

method warshall(adj: array2 <bool>) returns (R: array2<bool>)
    requires adj.Length0 == adj.Length1
    ensures R.Length0 == adj.Length0 && R.Length1 == adj.Length1
    ensures forall u, v | 0 <= u < adj.Length0 && 0 <= v < adj.Length1:: R[u,v] <==> existsPath(adj, u, v, adj.Length0)

{
    var n := adj.Length0;
    R := new bool[n,n];

    var i := 0;
    while i < n 
        decreases n - i
        invariant (0 <= i <= n) && (forall o,p | 0 <= o < i && 0 <= p < adj.Length1 :: R[o,p] <==> existsPath(adj, o, p, 0))
        
        {
            var j := 0;
            while j < n
                decreases n - j
                invariant (0 <= j <= n) && (forall t | 0 <= t < j :: R[i, t] <==> existsPath(adj, i, t, 0))
                invariant (0 <= i <= n) && (forall o,p | 0 <= o < i && 0 <= p < adj.Length1 :: R[o,p] <==> existsPath(adj, o, p, 0))
                
                {
                    R[i,j] := (i == j) || adj[i,j];
                    j := j + 1;
                }

                //assert forall t | 0 <= t < n :: R[i, t] <==> existsPath(adj, i, t, 0);
                i := i + 1;
        }

        var k := 0;
        while k < n
            decreases n - k
            invariant (0 <= k <= n) && (forall o,p | 0 <= o < n && 0 <= p < n:: R[o,p] <==> existsPath(adj, o, p, k))
            {
                var u := 0;
                while u < n 
                    decreases n - u
                    invariant (0 <= u <= n) && (forall a,b | 0 <= a < u && 0 <= b < n :: R[a,b] <==> existsPath(adj, a, b, k + 1)) && (forall z,w | u <= z < n && 0 <= w < n:: R[z,w] <==> existsPath(adj, z, w, k))
                    {
                        var v := 0;
                        while v < n
                            decreases n - v
                            invariant (0 <= v <= n) && (forall b | 0 <= b < v:: R[u,b] <==> existsPath(adj, u, b, k + 1)) && (forall a | v <= a < n:: R[u,a] <==> existsPath(adj, u, a, k))
                            invariant (0 <= u <= n) && (forall a,b | 0 <= a < u && 0 <= b < n:: R[a,b] <==> existsPath(adj, a, b, k + 1)) && (forall z,w | u < z < n && 0 <= w < n:: R[z,w] <==> existsPath(adj, z, w, k))
                            {
                                R[u,v] := R[u,v] || (R[k,v] && R[u,k]);
                                v := v + 1;
                            }

                            u := u + 1;
                    }

                    k := k + 1;
            }
    
}


method Main()
{
  var adj := new bool[3,3];
  adj[0,0] := false; adj[0,1] := true;  adj[0,2] := false;
  adj[1,0] := false; adj[1,1] := false; adj[1,2] := true;
  adj[2,0] := false; adj[2,1] := false; adj[2,2] := false;

  var R := warshall(adj);

  var i := 0;
  while i < 3
  {
    var j := 0;
    while j < 3
    {
      print R[i,j], " ";
      j := j + 1;
    }
    print "\n";
    i := i + 1;
  }
}
