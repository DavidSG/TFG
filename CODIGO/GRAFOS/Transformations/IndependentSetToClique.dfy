include "../Auxiliar/Graph.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/Clique.dfy"

function IndependentSet_to_Clique(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (complement(graph),k)
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
        var clique:set<Node> :| clique <= Vgraph.0 && isClique(clique,Vgraph) && |clique| >= Vk;

        var IndepSet:set<Node> := clique;

        // Demostracion: isIndependentSet(IndepSet,graph)
        auxIndependentSet (IndepSet, graph); 
        
        assert IndepSet <= graph.0 && isIndependentSet(IndepSet,graph) && |IndepSet| >= k;
    }
}

lemma IndependentSet_Clique2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_Clique(graph,k);
          IndependentSet(graph,k) ==> Clique(Vgraph,Vk)
{
    if (IndependentSet(graph,k)) {
        var (Vgraph,Vk) := IndependentSet_to_Clique(graph,k);
        var IndepSet:set<Node> :| IndepSet <= graph.0 && isIndependentSet(IndepSet,graph) && |IndepSet| >= k;

        var clique:set<Node> := IndepSet;

        // Demostracion 1 : isClique(clique,Vgraph.1)
        auxIndependentSet(IndepSet, graph); 

        assert clique <= Vgraph.0 && isClique(clique,Vgraph) && |clique| >= Vk;
    }
}
