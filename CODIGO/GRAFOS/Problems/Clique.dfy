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

/*function FSumNat(e : Edge) : nat
  requires |e| == 2
{ 
  var u,v;
}

function minEdge(E:set<Edge>): (min:Edge)
  requires E != {}
  ensures forall e | e in E :: 


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
*/

