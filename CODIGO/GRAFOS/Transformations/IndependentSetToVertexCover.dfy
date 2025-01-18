include "../Auxiliar/Graph.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/VertexCover.dfy"

function IndependentSet_to_VertexCover(graph:Graph, k:int) : (r:(Graph,int))
{
    (graph,|graph.0|-k)
}

lemma IndependentSet_VertexCover(graph:Graph, k:int)
  ensures var (Vgraph,Vk):= IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) <==> IndependentSet(Vgraph,Vk)
{ 
    IndependentSet_VertexCover1(graph,k);
    IndependentSet_VertexCover2(graph,k);
}

lemma IndependentSet_VertexCover1(graph:Graph, k:int)
    ensures var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) <== VertexCover(Vgraph,Vk)
{   
    var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
    if (VertexCover(Vgraph,Vk)) {
        
    }
}

lemma IndependentSet_VertexCover2(graph:Graph, k:int)
    ensures var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) ==> VertexCover(Vgraph,Vk)
{

    if (IndependentSet(graph,k)) {
        
    }
}
