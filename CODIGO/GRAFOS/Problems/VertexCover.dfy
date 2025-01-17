include "../Auxiliar/Node.dfy"

ghost predicate VertexCover(graph:set<Node>, k:int)
{
  var A: set<set<Node>> := (set node | node in graph :: {node});
  exists s:set<Node> :: isVertexCover(s,A) && |s| <= k && s <= graph
}

ghost predicate isVertexCover(s:set<Node>, A:set<set<Node>>)
{
  (forall a | a in A :: |s * a| != 0)
}