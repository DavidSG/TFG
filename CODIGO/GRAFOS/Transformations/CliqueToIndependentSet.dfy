include "../Auxiliar/Graph.dfy"
include "../Problems/Clique.dfy"
include "../Problems/IndependentSet.dfy"

function Clique_to_IndependentSet(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
    ensures isValidGraph(r.0)
{
    (complement(graph),k)
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
        // Encontramos una solucion para IndependentSet(Vgraph,Vk)
        var IndepSet:set<Node> :| IndepSet <= Vgraph.0 && isIndependentSet(IndepSet,Vgraph) && |IndepSet| >= Vk;
        
        // Clique será nuestra solución a Clique(graph,k)
        var clique:set<Node> := IndepSet;

        // Empleamos la siguiente definición alternativa para Independent set
        auxIndependentSet(IndepSet,Vgraph);
        assert forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in Vgraph.1;

        // Si existe un conjunto independiente en el grafo complementario Vgraph, 
        // entonces el mismo conjunto de nodos forma un clique en el grafo original.
        assert isClique(clique,graph) && |clique| >= k && clique <= graph.0;
    }
}

lemma Clique_IndependentSet2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := Clique_to_IndependentSet(graph,k);
          Clique(graph,k) ==> IndependentSet(Vgraph,Vk)
{
    if (Clique(graph,k)) {
        var (Vgraph,Vk) := Clique_to_IndependentSet(graph,k);

        // Encontramos una solución para Clique(graph,k)
        var clique:set<Node> :| clique <= graph.0 && isClique(clique,graph) && |clique| >= k;

        // IndepSet será nuestra solución a IndependentSet(Vgraph,Vk)
        var IndepSet:set<Node> := clique;

        // Empleamos la definición alternativa para Independent Set
        auxIndependentSet(IndepSet,Vgraph);
        assert forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in Vgraph.1;

        // Si existe un clique en el grafo original, 
        // entonces el mismo conjunto de nodos forma un idependent set en Vgraph.
        assert isIndependentSet(IndepSet,Vgraph) && |IndepSet| >= Vk && IndepSet <= Vgraph.0;
    }
}
