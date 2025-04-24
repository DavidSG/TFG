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
        // Encontramos una solución para Clique(Vgraph,Vk)
        var clique:set<Node> :| clique <= Vgraph.0 && |clique| >= Vk && isClique(clique,Vgraph); 

        // IndepSet será nuestra solución a IndependentSet(graph,k)
        var IndepSet:set<Node> := clique;

        // Empleamos la siguiente definición alternativa para Independent Set
        auxIndependentSet (IndepSet, graph); 
        assert forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1;
        
        // Demostramos que IndepSet es un conjunto independiente en el grafo original
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

        // Encontramos una solución para IndependentSet(graph,k)
        var IndepSet:set<Node> :| IndepSet <= graph.0 && |IndepSet| >= k && isIndependentSet(IndepSet,graph);

        // clique será nuestra solución a Clique(Vgraph,Vk)
        var clique:set<Node> := IndepSet;

        // Empleamos la siguiente definición alternativa para Independent Set
        auxIndependentSet(IndepSet, graph); 
        assert forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1;

        // Demostramos que clique es un clique en el grafo Vgraph
        assert clique <= Vgraph.0 && isClique(clique,Vgraph) && |clique| >= Vk;
    }
}