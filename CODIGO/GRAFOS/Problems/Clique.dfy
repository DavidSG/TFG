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

function minEdge(m:multiset<int>): (l:int)
  requires m != multiset{}
  ensures l in m && (forall x | x in m :: l <= x) 
{ HasMinimumInt(m);
  var x :| x in m && (forall y | y in m :: x <= y); 
  x
}

method {:verify true} checkClique(graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == (I <= graph.0 && isClique(I,graph) && |I| >= k)
{
  var E:set<Edge> := graph.1;
  while (E != {}) {
    var e := minEdge(E);
  }
  b := I <= graph.0 && |I| >= k;
}


