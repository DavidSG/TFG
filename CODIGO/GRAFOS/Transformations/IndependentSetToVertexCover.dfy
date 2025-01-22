include "../Auxiliar/Graph.dfy"
include "../Problems/IndependentSet.dfy"
include "../Problems/VertexCover.dfy"

function IndependentSet_to_VertexCover(graph:Graph, k:int) : (r:(Graph,int))
    requires isValidGraph(graph)
{
    (graph,|graph.0|-k)
}

lemma IndependentSet_VertexCover(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk):= IndependentSet_to_VertexCover(graph,k);
        IndependentSet(graph,k) <==> VertexCover(Vgraph,Vk)
{ 
    IndependentSet_VertexCover1(graph,k);
    IndependentSet_VertexCover2(graph,k);
}

lemma aux (IndepSet:set<Node>, vCover:set<Node>, graph:Graph)
    requires isValidGraph(graph) && isIndependentSet(IndepSet, graph.1) && isVertexCover(vCover, graph.1)
    requires IndepSet + vCover == graph.0
    requires IndepSet * vCover == {}
    ensures forall e | e in graph.1 :: |IndepSet * e| + |vCover * e| == |e|
    decreases |graph.1|
{   
    if (|graph.1| == 0) {
        assert forall e | e in graph.1 :: |IndepSet * e| + |vCover * e| == |e|;
    }
    else {
        var e:set<Node> :| e in graph.1;
        assert |e| == 2;

        assert |IndepSet * e| <= 1;
        if (|IndepSet * e| == 0) {
            assert |vCover * e| == 2;
        }
        else if (|IndepSet * e| == 1) {
            assume |vCover * e| == 1;
        }

        aux (IndepSet,vCover,(graph.0,graph.1-{e}));
        assert forall e | e in graph.1 :: |IndepSet * e| + |vCover * e| == |e|;
    }
}


lemma IndependentSet_VertexCover1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) <== VertexCover(Vgraph,Vk)
{   
    var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
    if (VertexCover(Vgraph,Vk)) {
        var vCover:set<Node> :| isVertexCover(vCover,Vgraph.1) && |vCover| <= Vk && vCover <= Vgraph.0;

        var IndepSet:set<Node> := graph.0 - vCover;

        // Demostracion 1 : isIndependentSet(IndepSet,graph.1)
        aux (IndepSet, vCover, graph); // Por cada arista, hay uno o dos elementos de vertexCover, lo que significa que debe haber uno de IndepSet        
        
        assert isIndependentSet(IndepSet,graph.1) && |IndepSet| >= k && IndepSet <= graph.0;
    }
}

lemma IndependentSet_VertexCover2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
          IndependentSet(graph,k) ==> VertexCover(Vgraph,Vk)
{
    if (IndependentSet(graph,k)) {
        var (Vgraph,Vk) := IndependentSet_to_VertexCover(graph,k);
        var IndepSet:set<Node> :| isIndependentSet(IndepSet,graph.1) && |IndepSet| >= k && IndepSet <= graph.0;

        var vCover:set<Node> := graph.0 - IndepSet;

        // Demostracion 1 : isVertexCover(vCover,graph.1)
        aux(IndepSet, vCover, graph); 

        assert isVertexCover(vCover,Vgraph.1) && |vCover| <= Vk && vCover <= Vgraph.0;
    }
}
