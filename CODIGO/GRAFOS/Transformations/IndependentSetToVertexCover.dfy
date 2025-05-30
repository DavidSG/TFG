include "../Auxiliar/Graph.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/VertexCover.dfy"

function IndependentSet_to_VertexCover(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (graph,|graph.0|-k)
}

lemma IndependentSet_VertexCover(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk):= IndependentSet_to_VertexCover(graph,k);
        IndependentSet(graph,k) <==> VertexCover(Vgraph,Vk)
{ 
    IndependentSet_VertexCover1(graph,k);
    IndependentSet_VertexCover2(graph,k);
}

lemma IndependentSet_VertexCover1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) <== VertexCover(Vgraph,Vk)
{   
    var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
    if (VertexCover(Vgraph,Vk)) {
        // Encontramos una solución a VertexCover(Vgraph,Vk)
        var vCover:set<Node> :| vCover <= Vgraph.0 && isVertexCover(vCover,Vgraph) && |vCover| <= Vk;

        // IndepSet será nuestra solución a IndependentSet(graph,k)
        // Lo definimos como el conjunto de los vertices que están en graph.0 pero no están en vCover
        var IndepSet:set<Node> := graph.0 - vCover;

        // Si asumimos que IndepSet + vCover == V (vértices) entonces para cada arista
        // hay dos opciones:
        // Ambos vértices pertenecen a vCover y 0 pertenecen a indepSet
        // Un vértice pertenece a vCover y otro a IndepSet
        assert forall e | e in graph.1 :: IndepSet * e + vCover * e == e;

        
        assert IndepSet <= graph.0 && isIndependentSet(IndepSet,graph) && |IndepSet| >= k;
    }
}

lemma IndependentSet_VertexCover2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) ==> VertexCover(Vgraph,Vk)
{
    if (IndependentSet(graph,k)) {
        var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);

        // Encontramos una solución a IndependentSet(graph,k)
        var IndepSet:set<Node> :| IndepSet <= graph.0 && isIndependentSet(IndepSet,graph) && |IndepSet| >= k;

        // vCover será nuestra solución a VertexCover(Vgraph,Vk)
        // Lo definimos como el conjunto de los vertices que están en graph.0 pero no están en indepSet
        var vCover:set<Node> := graph.0 - IndepSet;

        // Si asumimos que IndepSet + vCover == V (vértices) entonces para cada arista
        // hay dos opciones:
        // Ambos vértices pertenecen a vCover y 0 pertenecen a indepSet
        // Un vértice pertenece a vCover y otro a IndepSet
        assert forall e | e in graph.1 :: IndepSet * e + vCover * e == e;

        assert vCover <= Vgraph.0 && isVertexCover(vCover,Vgraph) && |vCover| <= Vk;
    }
}
