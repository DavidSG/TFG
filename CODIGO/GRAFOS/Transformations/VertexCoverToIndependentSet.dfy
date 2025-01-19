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

lemma aux (IndepSet:set<Node>, vCover:set<Node>, graph:Graph)
    requires IndepSet + vCover == graph.0
    requires IndepSet * vCover == {}
    ensures forall e | e in graph.1 :: |IndepSet * e| + |vCover * e| == |e|


lemma VertexCover_IndependentSet1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);
          VertexCover(graph,k) <== IndependentSet(Vgraph,Vk)
{   
    var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);
    if (IndependentSet(Vgraph,Vk)) {
        var IndepSet:set<Node> :| isIndependentSet(IndepSet,Vgraph.1) && |IndepSet| >= Vk && IndepSet <= Vgraph.0;

        var vCover:set<Node> := graph.0 - IndepSet;

        // Demostracion 1 : isVertexCover(IndepSet,graph.1)
        aux (IndepSet, vCover, graph); // Por cada arista, hay uno o dos elementos de IndependentSet, lo que significa que debe haber uno de IndepSet        
        
        assert isVertexCover(vCover,graph.1) && |vCover| <= k && vCover <= graph.0;
    }
}

lemma VertexCover_IndependentSet2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);
          VertexCover(graph,k) ==> IndependentSet(Vgraph,Vk)
{
    if (VertexCover(graph,k)) {
        var (Vgraph,Vk) := VertexCover_to_IndependentSet(graph,k);
        var vCover:set<Node> :| isVertexCover(vCover,graph.1) && |vCover| <= k && vCover <= graph.0;

        var IndepSet:set<Node> := graph.0 - vCover;

        // Demostracion 1 : isIndependentSet(vCover,graph.1)
        aux(IndepSet, vCover, graph); 

        assert isIndependentSet(IndepSet,Vgraph.1) && |IndepSet| >= Vk && vCover <= Vgraph.0;
    }
}
