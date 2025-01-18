include "../Auxiliar/Node.dfy"

ghost predicate Clique(graph : set<Node>, k:int)
reads graph
{
  var A: set<set<Node>> := (set node, adj | node in graph && adj in node.adyacentes:: {node, adj});
  exists s:set<Node> :: isClique(s,A) && |s| >= k && s <= graph
}

ghost predicate isClique(s:set<Node>, A:set<set<Node>>)
{
  (forall u,v | u in s && v in s && u != v :: {u,v} in A)
}