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

lemma aux (IndepSet:set<Node>, vCover:set<Node>, graph:Graph)
    requires IndepSet + vCover == graph.0
    requires IndepSet * vCover == {}
    ensures forall e | e in graph.1 :: |IndepSet * e| + |vCover * e| == |e|

lemma VertexCover_Clique1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);
          VertexCover(graph,k) <== Clique(Vgraph,Vk)
{   
    var (Vgraph,Vk) := VertexCover_to_Clique(graph,k);
    if (Clique(Vgraph,Vk)) {
        var clique:set<Node> :| clique <= Vgraph.0 && isClique(clique,Vgraph) && |clique| >= Vk;

        var IndepSet:set<Node> := clique;

        var vCover:set<Node> := graph.0 - IndepSet;

        // Demostracion 1 : isVertexCover(VertexCover,graph.1)
        auxIndependentSet(IndepSet,graph);
        aux (IndepSet, vCover, graph);

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

        var IndepSet:set<Node> := graph.0 - vCover;

        var clique:set<Node> := IndepSet;

        // Demostracion 1 : isClique(IndepSet,Vgraph.1)
        auxIndependentSet(IndepSet,Vgraph);

        assert clique <= Vgraph.0 && isClique(clique,Vgraph) && |clique| >= Vk;
    }
}
