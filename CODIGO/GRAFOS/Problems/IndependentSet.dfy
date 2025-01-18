include "../Auxiliar/Node.dfy"

ghost predicate IndependentSet(graph:set<Node>, k:int)
reads graph
{
  var A: set<set<Node>> := (set node, adj | node in graph && adj in node.adyacentes:: {node, adj});
  exists s:set<Node> :: isIndependentSet(s,A) && |s| >= k && s <= graph
}

ghost predicate isIndependentSet(s:set<Node>, A:set<set<Node>>)
{
  forall a | a in A :: |s * a| <= 1
}
