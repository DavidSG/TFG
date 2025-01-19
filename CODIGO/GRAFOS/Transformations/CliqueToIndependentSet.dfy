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

lemma aux (IndepSet:set<Node>, graph:Graph)
    requires isIndependentSet(IndepSet, graph.1)
    ensures forall u,v | u in IndepSet && v in IndepSet && u != v :: {u,v} !in graph.1

lemma aux2 (clique:set<Node>, graph:Graph)
    requires isClique(clique, graph.1)
    ensures forall u,v | u in clique && v in clique && u != v :: {u,v} !in invert(graph).1
    ensures forall e | e in invert(graph).1 :: |clique * e| < 2

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
        aux(IndepSet,Vgraph);

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
        aux2(clique,graph);

        assert isIndependentSet(IndepSet,Vgraph.1) && |IndepSet| >= Vk && IndepSet <= Vgraph.0;
    }
}
