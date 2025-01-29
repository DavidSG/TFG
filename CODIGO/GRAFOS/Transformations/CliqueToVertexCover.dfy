include "../Auxiliar/Graph.dfy"
include "../Problems/Clique.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/VertexCover.dfy"

function Clique_to_VertexCover(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (complement(graph),|graph.0|-k)
}

lemma Clique_VertexCover(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk):= Clique_to_VertexCover(graph,k);
        Clique(graph,k) <==> VertexCover(Vgraph,Vk)
{
    Clique_VertexCover1(graph,k);
    Clique_VertexCover2(graph,k);
}

lemma Clique_VertexCover1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := Clique_to_VertexCover(graph,k);
          Clique(graph,k) <== VertexCover(Vgraph,Vk)
{   
    var (Vgraph,Vk) := Clique_to_VertexCover(graph,k);
    if (VertexCover(Vgraph,Vk)) {
        var vCover:set<Node> :| vCover <= Vgraph.0 && isVertexCover(vCover,Vgraph) && |vCover| <= Vk;

        var IndepSet:set<Node> := Vgraph.0 - vCover;

        var clique:set<Node> := IndepSet;

        // Demostracion 1 : isClique(clique,graph.1)
        auxIndependentSet(IndepSet,Vgraph);
        assert forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in Vgraph.1;

        assert clique <= graph.0 && isClique(clique,graph) && |clique| >= k;
    }
}

lemma Clique_VertexCover2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := Clique_to_VertexCover(graph,k);
          Clique(graph,k) ==> VertexCover(Vgraph,Vk)
{
    if (Clique(graph,k)) {
        var (Vgraph,Vk) := Clique_to_VertexCover(graph,k);
        var clique:set<Node> :| clique <= graph.0 && isClique(clique,graph) && |clique| >= k;

        var IndepSet:set<Node> := clique;

        var vCover:set<Node> := graph.0 - IndepSet;

        // Demostracion 1 : isVertexCover(IndepSet,Vgraph.1)
        auxIndependentSet(IndepSet,Vgraph);

        assert isVertexCover(vCover,Vgraph) && |vCover| <= Vk && vCover <= Vgraph.0;
    }
}
