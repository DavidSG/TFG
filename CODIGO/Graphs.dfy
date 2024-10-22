method Main() {
  print "Hello, Dafny!\n";
  // Create the nodes
  var a := new Node("a");
  var b := new Node("b");
  var c := new Node("c");
  var d := new Node("d");
  var e := new Node("e");
  
  // Define adjacency lists (neighboring nodes)
  a.adyacentes := [b, c, d];            // a is adjacent to b, c
  b.adyacentes := [a, c, d, e];      // b is adjacent to a, c, d, e
  c.adyacentes := [a, b, d];         // c is adjacent to a, b, d
  d.adyacentes := [a, b, c, e];         // d is adjacent to b, c, e
  e.adyacentes := [b, d];            // e is adjacent to b, d

  var graph: set<Node> := {a,b,c,d,e};
  var A: set<set<Node>> := (set node, adj | node in graph && adj in node.adyacentes :: {node, adj});
  var inverseA: set<set<Node>> := (set node, adj | node in graph && adj in node.adyacentes :: {node, adj});
  
  
  // Print the result
  print "Grouped sets by elements from U:\n";
  print "A: ";
  while ( A != {} ) {
      var pair: set<Node> :| pair in A;
      A := A - { pair };
      print "{";
      while ( pair != {} ) {
        var e :| e in pair;
        pair := pair - { e };
        print e.v; 
      }
      print "} ";
  } 

  while ( inverseA != {} ) {
      var pair: set<Node> :| pair in A;
      inverseA := inverseA - { pair };
      print "{";
      while ( pair != {} ) {
        var e :| e in pair;
        pair := pair - { e };
        print e.v; 
      }
      print "} ";
  } 
}

class Node
{
  var v: string
  var adyacentes: set<Node> 
  constructor  (c: string) {
    v := c;
    adyacentes := {};  // Initialize as an empty sequence
  }
}

ghost predicate IndependentSet(graph:set<Node>, k:int)
{
  var A: set<set<Node>> := (set node | node in graph :: {node});
  exists s:set<Node> :: isIndependentSet(s,A) && |s| >= k && s <= graph
}

ghost predicate isIndependentSet(s:set<Node>, A:set<set<Node>>)
{
  (forall a | a in A :: |s * a| <= 1)
}

ghost predicate Clique(graph : set<Node>, k:int)
{
  var A: set<set<Node>> := (set node, adj | node in graph && adj in node.adyacentes :: {node, adj});
  exists s:set<Node> :: isClique(s,A) && |s| <= k && s <= graph
}

ghost predicate isClique(s:set<Node>, A:set<set<Node>>)
{
  (forall u,v | u in s && v in s && u != v :: {u,v} in A)
}

// Una cobertura es un subconjunto de vértices s <= V 
// tal que si {u,v} in A, entonces u in V o v in V (o ambos).
ghost predicate VertexCover(graph:set<Node>, k:int)
{
  var A: set<set<Node>> := (set node, adj | node in graph && adj in node.adyacentes :: {node, adj});
  exists s:set<Node> :: isVertexCover(s,A) && |s| <= k && s <= graph
}

ghost predicate isVertexCover(s:set<Node>, A:set<set<Node>>)
{
  (forall a | a in A :: |s * a| != 0)
}

// INDEPENDENT SET -> VERTEX COVER
function IndependentSet_to_VertexCover(graph:set<Node>, k:int) : (r:(set<Node>,int)) {
  (graph, |graph|-k)
}


lemma {:axiom} IndependentSet_VertexCover<T>(graph:set<Node>, k:int)
  ensures var (graph2,k2) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) <==> VertexCover(graph2,k2)


// INDEPENDENT SET -> CLIQUE
function IndependentSet_to_Clique(graph:set<Node>, k:int) : (r:(set<Node>,int)) { 
  var test: set<Node> := graph;
  forall x in mySet { 
  ((set n1,n2 | n1 in graph && n2 in graph && n1 != n2 && n2 !in n1.adyacentes :: n1), |graph|-k)
}


lemma {:axiom} IndependentSet_Clique<T>(graph:set<Node>, k:int)
  ensures var (graph2,k2) := IndependentSet_to_Clique(graph,k);
          IndependentSet(graph,k) <==> Clique(graph2,k2)
