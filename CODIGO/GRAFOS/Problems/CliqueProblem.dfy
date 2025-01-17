include "../Auxiliar/Node.dfy"

ghost predicate Clique(graph : set<Node>, k:int)
{
  var A: set<set<Node>> := (set node | node in graph :: {node});
  exists s:set<Node> :: isClique(s,A) && |s| <= k && s <= graph
}

ghost predicate isClique(s:set<Node>, A:set<set<Node>>)
{
  (forall u,v | u in s && v in s && u != v :: {u,v} in A)
}