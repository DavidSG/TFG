include "../Auxiliar/Graph.dfy"

ghost predicate VertexCover(graph:Graph, k:int)
{
  exists s:set<Node> :: isVertexCover(s,graph.1) && |s| <= k && s <= graph.0
}

ghost predicate isVertexCover(s:set<Node>, A:set<set<Node>>)
{
  forall a | a in A :: |s * a| != 0
}