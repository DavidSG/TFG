include "../Auxiliar/Graph.dfy"

ghost predicate IndependentSet(graph:Graph, k:int)
{
  exists s:set<Node> :: isIndependentSet(s,graph.1) && |s| >= k && s <= graph.0
}

ghost predicate isIndependentSet(s:set<Node>, E:set<Edge>)
{
  forall e | e in E :: |s * e| <= 1
}

lemma auxIndependentSet (IndepSet:set<Node>, graph:Graph)
    requires isIndependentSet(IndepSet, graph.1)
    ensures forall e | e in graph.1 :: |IndepSet * e| <= 1 <==> forall u,v | u in graph.0 && v in graph.0 && u != v :: {u,v} !in graph.1;
