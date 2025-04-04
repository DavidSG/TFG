include "../Auxiliar/Graph.dfy"
include "../Problems/VertexCover.dfy"
include "../Problems/IndependentSet.dfy"

function VertexCover_to_IndependentSet(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (graph,|graph.0|-k)
}

lemma VertexCover_IndependentSet(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk):= VertexCover_to_IndependentSet(graph,k);
        VertexCover(graph,k) <==> IndependentSet(Vgraph,Vk)
{ 
    VertexCover_IndependentSet1(graph,k);
    VertexCover_IndependentSet2(graph,k);
}

lemma VertexCover_IndependentSet1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);
          VertexCover(graph,k) <== IndependentSet(Vgraph,Vk)
{   
    var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);
    if (IndependentSet(Vgraph,Vk)) {
        // Encontramos una solución a IndependentSet(Vgraph,Vk)
        var IndepSet:set<Node> :| IndepSet <= Vgraph.0 && isIndependentSet(IndepSet,Vgraph) && |IndepSet| >= Vk;

        // vCover será nuestra solución a VertexCover(graph,k)
        // Lo definimos como el conjunto de los vertices que están en graph.0 pero no están en vCover
        var vCover:set<Node> := graph.0 - IndepSet;

        // Si asumimos que IndepSet + vCover == V (vértices) entonces para cada arista
        // hay dos opciones:
        // Ambos vértices pertenecen a vCover y 0 pertenecen a indepSet
        // Un vértice pertenece a vCover y otro a IndepSet
        assert forall e | e in graph.1 :: IndepSet * e + vCover * e == e;
        
        assert vCover <= graph.0 && isVertexCover(vCover,graph) && |vCover| <= k;
    }
}

lemma VertexCover_IndependentSet2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);
          VertexCover(graph,k) ==> IndependentSet(Vgraph,Vk)
{
    if (VertexCover(graph,k)) {
        var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);

        // Encontramos una solución a IndependentSet(Vgraph,Vk)
        var vCover:set<Node> :| vCover <= graph.0 && isVertexCover(vCover,graph) && |vCover| <= k;

        // vCover será nuestra solución a VertexCover(graph,k)
        // Lo definimos como el conjunto de los vertices que están en graph.0 pero no están en vCover
        var IndepSet:set<Node> := graph.0 - vCover;

        // Si asumimos que IndepSet + vCover == V (vértices) entonces para cada arista
        // hay dos opciones:
        // Ambos vértices pertenecen a vCover y 0 pertenecen a indepSet
        // Un vértice pertenece a vCover y otro a IndepSet
        assert forall e | e in graph.1 :: IndepSet * e + vCover * e == e;

        assert IndepSet <= Vgraph.0 && isIndependentSet(IndepSet,Vgraph) && |IndepSet| >= Vk;
    }
}
