include "../Auxiliar/Graph.dfy"

ghost predicate VertexCover(graph:Graph, k:int)
requires isValidGraph(graph)
{
  exists s:set<Node> :: s <= graph.0 && isVertexCover(s,graph) && |s| <= k  
}

ghost predicate isVertexCover(s:set<Node>, graph:Graph)
requires isValidGraph(graph)
requires s <= graph.0
{
  forall e | e in graph.1 :: |s * e| > 0
}