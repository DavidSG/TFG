include "../Auxiliar/Graph.dfy"
include "../Problems/Clique.dfy"
include "../Problems/IndependentSet.dfy"

function Clique_to_IndependentSet(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (invert(graph),k)
}

lemma Clique_IndependentSet(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk):= Clique_to_IndependentSet(graph,k);
        Clique(graph,k) <==> IndependentSet(Vgraph,Vk)
{ 
    Clique_IndependentSet1(graph,k);
    Clique_IndependentSet2(graph,k);
}

lemma Clique_IndependentSet1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := Clique_to_IndependentSet(graph,k);
          Clique(graph,k) <== IndependentSet(Vgraph,Vk)
{   
    var (Vgraph,Vk) := Clique_to_IndependentSet(graph,k);
    if (IndependentSet(Vgraph,Vk)) {
        var IndepSet:set<Node> :| isIndependentSet(IndepSet,Vgraph.1) && |IndepSet| >= Vk && IndepSet <= Vgraph.0;

        var clique:set<Node> := IndepSet;

        // Demostracion 1 : isClique(clique,graph.1)
        auxIndependentSet(IndepSet,Vgraph);
        assert forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in Vgraph.1;

        assert isClique(clique,graph.1) && |clique| >= k && clique <= graph.0;
    }
}

lemma Clique_IndependentSet2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := Clique_to_IndependentSet(graph,k);
          Clique(graph,k) ==> IndependentSet(Vgraph,Vk)
{
    if (Clique(graph,k)) {
        var (Vgraph,Vk) := Clique_to_IndependentSet(graph,k);
        var clique:set<Node> :| isClique(clique,graph.1) && |clique| >= k && clique <= graph.0;

        var IndepSet:set<Node> := clique;

        // Demostracion 1 : isIndependentSet(IndepSet,graph.1)
        auxIndependentSet(IndepSet,Vgraph);

        assert isIndependentSet(IndepSet,Vgraph.1) && |IndepSet| >= Vk && IndepSet <= Vgraph.0;
    }
}
