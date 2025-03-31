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
    if (exists e | e in graph.1 :: |IndepSet * e| > 1){
      var e :| e in graph.1 && |IndepSet * e| > 1;
      var u,v :| u in graph.0 && v in graph.0 && u !=v && e == {u,v};
      intersect(IndepSet,graph,e,u,v);

      assert u in IndepSet && v in IndepSet && u != v && {u,v} in graph.1; //La contradiccion
      assert false;  }
  }
}


lemma auxIndependentSet2 (IndepSet:set<Node>, graph:Graph)
  requires isValidGraph(graph) && IndepSet <= graph.0
  ensures isIndependentSet(IndepSet,graph) ==> (forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1)

{
  if (isIndependentSet(IndepSet,graph)) {
  if (exists u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} in graph.1)
   { var u,v :| u in IndepSet && v in IndepSet && u != v && {u,v} in graph.1;
    
    assert {u,v} in graph.1 && IndepSet * {u,v} == {u,v} && |IndepSet * {u,v}| == 2;
    assert false;}
  }
  
}

method {:verify true} checkIndependentSet (graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == (I <= graph.0 && isIndependentSet(I,graph) && |I| >= k)
{
  var I1 := I;
  var b1:= true;
  while (I1 != {} && b1)
  invariant I1 <= I 
  invariant b1 == forall u,v | u in I-I1 && v in I && u != v ::{u,v} !in graph.1
  {
   var e1 := pick(I1); 
   var I2:= I; var b2:= true;
   while (I2 != {} && b2)
    invariant I2 <= I 
     invariant b2 == forall v | v in I-I2 && e1 != v ::{e1,v} !in graph.1
   { 
     var e2 := pick(I2); 
     I2:= I2-{e2};
     if (e1 != e2)
        {b2 := b2 && {e1,e2} !in graph.1;}
   }
   I1 := I1 - {e1};
   b1 := b1 && b2;
  }
   
  assert b1 == forall u,v | u in I && v in I && u != v :: {u,v} !in graph.1;
  if (I <= graph.0) {
    auxIndependentSet(I,graph);
  }

  b := I <= graph.0 && |I| >= k && b1;
}

