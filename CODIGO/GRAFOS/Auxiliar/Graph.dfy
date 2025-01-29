type Node = nat
type Edge = set<Node>

type Graph = (set<Node>, set<Edge>)


function invert (graph:Graph) : (r:Graph)
requires isValidGraph(graph)
ensures isValidGraph(r) 
{
    var allEdges:set<Edge> := (set n1,n2 | n1 in graph.0 && n2 in graph.0 && n1 != n2 :: {n1,n2});
    var invertGraph:Graph := (graph.0, allEdges-graph.1);
    (invertGraph)
}


predicate isValidGraph(graph: Graph)
{
    forall e | e in graph.1 :: 
    (|e| == 2 
     && exists u,v :: u in graph.0 && v in graph.0 && u != v && e == {u,v} 
    )
}

lemma intersect(s: set<Node>, graph:Graph, e: Edge)
requires isValidGraph(graph)
requires e in graph.1
requires s <= graph.0
ensures |s * e| <= 2 
ensures var u,v :| u in graph.0 && v in graph.0 && u != v && e == {u,v}; 
  s * e == {} || s * e == {u} || s * e == {v} || s * e == e 


