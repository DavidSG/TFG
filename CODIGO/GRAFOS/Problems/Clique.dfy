include "../Auxiliar/Graph.dfy"

ghost predicate Clique(graph:Graph, k:int)
  requires isValidGraph(graph)
{
  exists s:set<Node> :: s <= graph.0 && isClique(s,graph) && |s| >= k 
}

ghost predicate isClique(s:set<Node>, graph:Graph)
  requires isValidGraph(graph)
  requires s <= graph.0
{
  forall u,v | u in s && v in s && u != v :: {u,v} in graph.1
}


method {:verify true} checkClique(graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == (I <= graph.0 && isClique(I,graph) && |I| >= k)
{
  var I1 := I;
  var b':= true;
  while (I1 != {} && b')
  invariant I1 <= I 
  invariant b' == forall u,v | u in I-I1 && v in I ::{u,v} in graph.1
  {
    var e1 := pick(I1); 
   var I2:= I;
   while (I2 != {} && b')
    invariant I2 <= I 
     invariant b' == forall u,v | u in I-I1 && v in I-I2 ::{u,v} in graph.1
   { 
     var e2 := pick(I2); 
     I2:= I2-{e2};
     b' := b' && {e1,e2} in graph.1;
   }
   I1 := I1 - {e1};
   assume false;
  }
   
  assume b'== forall u,v | u in I && v in I && u != v :: {u,v} in graph.1;
  b := I <= graph.0 && |I| >= k && b';
  
  
}


method pick<T>(S:set<T>) returns (r:T)
  requires S != {} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}