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
    ensures (forall e | e in graph.1 :: |IndepSet * e| <= 1) <==> (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1)
{
  auxIndependentSet1(IndepSet,graph);
  auxIndependentSet2(IndepSet,graph);
}

lemma auxIndependentSet1 (IndepSet:set<Node>, graph:Graph)
  ensures (forall e | e in graph.1 :: |IndepSet * e| <= 1) <== (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1)
{
  if (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1) {
    

    assume forall e | e in graph.1 :: |IndepSet * e| <= 1;
  }
}


lemma auxIndependentSet2 (IndepSet:set<Node>, graph:Graph)
  ensures (forall e | e in graph.1 :: |IndepSet * e| <= 1) ==> (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1)

{
  if (forall e | e in graph.1 :: |IndepSet * e| <= 1) {
    assert forall e | e in graph.1 :: |IndepSet * e| == 0 || |IndepSet * e| == 1;

    assume forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1;
  }
  
}
