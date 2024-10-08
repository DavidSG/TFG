class Node
{
  var adyacentes: seq<Node> 
}

ghost predicate IndependentSet(graph:set<Node>, k:int)
{
  var A: set<set<Node>> := (set node, adj | node in graph && adj in node.adyacentes :: {node, adj});
  exists s:set<Node> :: isIndependentSet(s,A) && |s| >= k && s <= graph
}

ghost predicate isIndependentSet(s:set<Node>, A:set<set<Node>>)
{
  (forall a | a in A :: |s * a| <= 1)
}

ghost predicate CliqueProblem(graph : set<Node>, k:int)
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
function IndependentSet_to_VertexCoverGraph(graph:set<Node>, k:int) : set<Node> {
  (graph)
}

function IndependentSet_to_VertexCoverK(graph:set<Node>, k:int) : int {
  (|graph|-k)
}

lemma {:axiom} IndependentSet_VertexCover<T>(graph:set<Node>, k:int)
  ensures IndependentSet(graph,k) <==> VertexCover(IndependentSet_to_VertexCoverGraph(graph,k),IndependentSet_to_VertexCoverK(graph,k))

/*
// INDEPENDENT SET -> CLIQUE
function IndependentSet_to_CliqueGraph(graph:set<Node>, k:int) : set<Node> {
  
}

function IndependentSet_to_CliqueK(graph:set<Node>, k:int) : int {
  (k)
}

lemma {:axiom} IndependentSet_Clique<T>(graph:set<Node>, k:int)
  ensures IndependentSet(graph,k) <==> VertexCover(IndependentSet_to_CliqueGraph(graph,k),IndependentSet_to_CliqueK(graph,k))
{

}
*/