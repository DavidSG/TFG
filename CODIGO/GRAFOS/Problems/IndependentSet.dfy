include "../Auxiliar/Graph.dfy"

ghost predicate IndependentSet(graph:Graph, k:int)
{
  exists s:set<Node> :: isIndependentSet(s,graph.1) && |s| >= k && s <= graph.0
}

ghost predicate isIndependentSet(s:set<Node>, A:set<Edge>)
{
  forall a | a in A :: |s * a| <= 1
}
