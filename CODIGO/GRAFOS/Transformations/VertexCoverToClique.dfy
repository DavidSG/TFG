include "../Auxiliar/Graph.dfy"
include "../Problems/VertexCover.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/Clique.dfy"
include "../Problems/Clique.dfy"

include "../Transformations/VertexCoverToIndependentSet.dfy"
include "../Transformations/IndependentSetToClique.dfy"


function VertexCover_to_Clique(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (complement(graph),|graph.0|-k)
}

lemma VertexCover_Clique(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk):= VertexCover_to_Clique(graph,k);
        VertexCover(graph,k) <==> Clique(Vgraph,Vk)
{ 
    VertexCover_Clique1(graph,k);
    VertexCover_Clique2(graph,k);
}

lemma VertexCover_Clique1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);
          VertexCover(graph,k) <== Clique(Vgraph,Vk)
{   
    var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);
    if (Clique(Vgraph,Vk)) {

        IndependentSet_Clique1(graph,Vk);
        assert IndependentSet(graph,Vk) <== Clique(Vgraph,Vk);

        VertexCover_IndependentSet1(graph,k);
        assert VertexCover(graph,k) <== IndependentSet(graph,Vk);
        
    }
}

lemma VertexCover_Clique2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);
          VertexCover(graph,k) ==> Clique(Vgraph,Vk)
{
    if (VertexCover(graph,k)) {
        var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);

        VertexCover_IndependentSet2(graph,k);
        assert VertexCover(graph,k) ==> IndependentSet(graph,Vk);

        IndependentSet_Clique2(graph,Vk);
        assert IndependentSet(graph,Vk) ==> Clique(Vgraph,Vk);


    }
}
