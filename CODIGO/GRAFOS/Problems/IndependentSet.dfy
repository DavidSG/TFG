include "../Auxiliar/Node.dfy"

ghost predicate IndependentSet(graph:set<Node>, k:int)
{
  var A: set<set<Node>> := (set node | node in graph :: {node, node.adyacentes} /*adyacent*/);
  exists s:set<Node> :: isIndependentSet(s,A) && |s| >= k && s <= graph
}

ghost predicate isIndependentSet(s:set<Node>, A:set<set<Node>>)
{
  forall a | a in A :: |s * a| <= 1
}

