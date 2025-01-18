type Node = nat
type Edge = set<Node>

type Graph = (set<Node>, set<Edge>)


function invert (graph:Graph) : (r:Graph)
{
    var allEdges:set<Edge> := (set n1,n2 | n1 in graph.0 && n2 in graph.0 && n1 != n2 :: {n1,n2});
    var invertGraph:Graph := (graph.0, allEdges-graph.1);
    (invertGraph)
}


