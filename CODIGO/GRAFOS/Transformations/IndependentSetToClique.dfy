include "../Auxiliar/Graph.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/Clique.dfy"

function IndependentSet_to_Clique(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (invert(graph),k)
}

lemma IndependentSet_Clique(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk):= IndependentSet_to_Clique(graph,k);
        IndependentSet(graph,k) <==> Clique(Vgraph,Vk)
{ 
    IndependentSet_Clique1(graph,k);
    IndependentSet_Clique2(graph,k);
}


lemma IndependentSet_Clique1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_Clique(graph,k);
          IndependentSet(graph,k) <== Clique(Vgraph,Vk)
{   
    var (Vgraph,Vk) := IndependentSet_to_Clique(graph,k);
    if (Clique(Vgraph,Vk)) {
        var clique:set<Node> :| isClique(clique,Vgraph.1) && |clique| >= Vk && clique <= Vgraph.0;

        var IndepSet:set<Node> := clique;

        // Demostracion 1 : isIndependentSet(IndepSet,graph.1)
        auxIndependentSet (IndepSet, graph); 
        
        assert isIndependentSet(IndepSet,graph.1) && |IndepSet| >= k && IndepSet <= graph.0;
    }
}

lemma IndependentSet_Clique2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_Clique(graph,k);
          IndependentSet(graph,k) ==> Clique(Vgraph,Vk)
{
    if (IndependentSet(graph,k)) {
        var (Vgraph,Vk) := IndependentSet_to_Clique(graph,k);
        var IndepSet:set<Node> :| isIndependentSet(IndepSet,graph.1) && |IndepSet| >= k && IndepSet <= graph.0;

        var clique:set<Node> := IndepSet;

        // Demostracion 1 : isClique(clique,Vgraph.1)
        auxIndependentSet(IndepSet, graph); 

        assert isClique(clique,Vgraph.1) && |clique| >= Vk && clique <= Vgraph.0;
    }
}
