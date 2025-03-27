include "../Auxiliar/Graph.dfy"

ghost predicate VertexCover(graph:Graph, k:int)
requires isValidGraph(graph)
{
  exists s:set<Node> :: s <= graph.0 && isVertexCover(s,graph) && |s| <= k  
}

ghost predicate isVertexCover(s:set<Node>, graph:Graph)
requires isValidGraph(graph)
requires s <= graph.0
{
  forall e | e in graph.1 :: |s * e| > 0
}


method {:verify true} checkVertexCover (graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == (I <= graph.0 && isVertexCover(I,graph) && |I| >= k)
{
  var edges := graph.1;
  var b1:= true;
  while (edges != {} && b1)
  invariant edges <= graph.1
  invariant b1 == forall e | e in graph.1 - edges :: |I * e| > 0
  {
    var e1 := pick(edges); 
    {b1 := b1 && |I * e1| > 0;}

    edges := edges - {e1};
  }
   
  assert b1 == forall e | e in graph.1 :: |I * e| > 0;
  b := I <= graph.0 && |I| >= k && b1;
}