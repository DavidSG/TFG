include "../Auxiliar/Graph.dfy"

ghost predicate IndependentSet(graph:Graph, k:int)
  requires isValidGraph(graph)
{
  exists s:set<Node> :: s <= graph.0 && isIndependentSet(s,graph) && |s| >= k 
}

ghost predicate isIndependentSet(s:set<Node>, graph:Graph)
requires isValidGraph(graph)
requires  s <= graph.0
{
  forall e | e in graph.1 :: |s * e| <= 1
}

lemma auxIndependentSet (IndepSet:set<Node>, graph:Graph)
    requires isValidGraph(graph) && IndepSet <= graph.0 
    ensures isIndependentSet(IndepSet,graph) <==> (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1)
{
  auxIndependentSet1(IndepSet,graph);
  auxIndependentSet2(IndepSet,graph);
}

lemma auxIndependentSet1 (IndepSet:set<Node>, graph:Graph)
  requires isValidGraph(graph) && IndepSet <= graph.0
  ensures isIndependentSet(IndepSet,graph) <== (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1)
{
  if (forall w,z | w in IndepSet && z in IndepSet && w != z :: {w,z} !in graph.1) {
      assume exists e | e in graph.1 :: |IndepSet * e| > 1;
      var e :| e in graph.1 && |IndepSet * e| > 1;
      var u,v :| u in graph.0 && v in graph.0 && u !=v && e == {u,v};
      intersect(IndepSet,graph,e);

      assert u in IndepSet && v in IndepSet && u != v && {u,v} in graph.1; //La contradiccion
      assert false;  
  }
}


lemma auxIndependentSet2 (IndepSet:set<Node>, graph:Graph)
  requires isValidGraph(graph) && IndepSet <= graph.0
  ensures isIndependentSet(IndepSet,graph) ==> (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1)

{
  if (isIndependentSet(IndepSet,graph)) {
    assume exists u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} in graph.1;
    var u,v :| u in IndepSet && v in IndepSet && u != v && {u,v} in graph.1;
    
    assert {u,v} in graph.1 && IndepSet * {u,v} == {u,v} && |IndepSet * {u,v}| == 2;
    assert false;
  }
  
}
