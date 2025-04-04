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

method checkClique(graph:Graph, k:int, I:set<Node>) returns (b:bool)
  requires isValidGraph(graph)
  ensures b == (I <= graph.0 && isClique(I,graph) && |I| >= k)
{
  // Con el primer bucle iteramos todos los elementos u de I1
  var I1 := I;
  var b1:= true;
  while (I1 != {} && b1)
  invariant I1 <= I 
  // Todos los elementos u explorados hasta el momento cumplen que todas las parejas 
  // {u,v}, donde v es otro elemento de I, son aristas del grafo (y por tanto forman un clique)
  invariant b1 == forall u,v | u in I-I1 && v in I && u != v ::{u,v} in graph.1
  {
    // En el segundo bucle iteramos todos los elementos v
   var e1 := pick(I1); 
   var I2:= I; var b2:= true;
   while (I2 != {} && b2)
    invariant I2 <= I 
    // Todos los elementos v explorados hasta el momento cumplen que todas las parejas 
    // {e1,v}, donde e1 es el elemento seleccionado de I1, son aristas del grafo (y por tanto forman un clique)
     invariant b2 == forall v | v in I-I2 && e1 != v ::{e1,v} in graph.1
   { 
     var e2 := pick(I2); 
     I2:= I2-{e2};
     if (e1 != e2)
        {b2 := b2 && {e1,e2} in graph.1;}
   }
   I1 := I1 - {e1};
   b1 := b1 && b2;
  }
   
  assert b1 == forall u,v | u in I && v in I && u != v :: {u,v} in graph.1;
  b := I <= graph.0 && |I| >= k && b1;
  
}


