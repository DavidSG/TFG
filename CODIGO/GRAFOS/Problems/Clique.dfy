include "../Auxiliar/Graph.dfy"

ghost predicate Clique(graph:Graph, k:int)
{
  exists s:set<Node> :: isClique(s,graph.1) && |s| >= k && s <= graph.0
}

ghost predicate isClique(s:set<Node>, E:set<set<Node>>)
{
  forall u,v | u in s && v in s && u != v :: {u,v} in E
}