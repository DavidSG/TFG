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
        var vCover:set<Node> :| isVertexCover(vCover,Vgraph.1) && |vCover| <= Vk && vCover <= Vgraph.0;

        var IndepSet:set<Node> := graph.0 - vCover;

        // Demostracion 1 : isIndependentSet(IndepSet,graph.1)
        assert forall e | e in graph.1 :: IndepSet * e + vCover * e == e;
        
        assert isIndependentSet(IndepSet,graph.1) && |IndepSet| >= k && IndepSet <= graph.0;
    }
}

lemma IndependentSet_VertexCover2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) ==> VertexCover(Vgraph,Vk)
{
    if (IndependentSet(graph,k)) {
        var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
        var IndepSet:set<Node> :| isIndependentSet(IndepSet,graph.1) && |IndepSet| >= k && IndepSet <= graph.0;

        var vCover:set<Node> := graph.0 - IndepSet;

        // Demostracion 1 : isVertexCover(vCover,graph.1)
        assert forall e | e in graph.1 :: IndepSet * e + vCover * e == e;

        assert isVertexCover(vCover,Vgraph.1) && |vCover| <= Vk && vCover <= Vgraph.0;
    }
}
