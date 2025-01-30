include "../Auxiliar/Graph.dfy"
include "../Problems/VertexCover.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/Clique.dfy"

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
        var clique:set<Node> :| clique <= Vgraph.0 && isClique(clique,Vgraph) && |clique| >= Vk;

        var vCover:set<Node> := graph.0 - clique;

        assert vCover <= graph.0 && isVertexCover(vCover,graph) && |vCover| <= k;
    }
}

lemma VertexCover_Clique2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);
          VertexCover(graph,k) ==> Clique(Vgraph,Vk)
{
    if (VertexCover(graph,k)) {
        var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);
        var vCover:set<Node> :| vCover <= graph.0 && isVertexCover(vCover,graph) && |vCover| <= k;

        var clique:set<Node> := graph.0 - vCover;

        assert clique <= Vgraph.0 && isClique(clique,Vgraph) && |clique| >= Vk;
    }
}
