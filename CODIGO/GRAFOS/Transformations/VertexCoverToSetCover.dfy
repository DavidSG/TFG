include "../Auxiliar/Graph.dfy"
include "../Problems/VertexCover.dfy"
include "../../SETS/Problems/SetCover.dfy"

function edges(graph:Graph,v:nat):set<set<nat>>
    requires isValidGraph(graph)
    requires v in graph.0
{ set e | e in graph.1 && v in e}



function VertexCover_to_SetCover(graph:Graph, k:int) : (r:(set<set<nat>>,set<set<set<nat>>>,int))
    requires isValidGraph(graph)
    ensures isCover(r.0,r.1)
{ isSetCover(graph);
 (graph.1,set v | v in graph.0 :: edges(graph,v) ,if k < 0 then 0 else k)
}


lemma isSetCover(graph:Graph)
requires isValidGraph(graph)
ensures isCover(graph.1,set v | v in graph.0 :: edges(graph,v))
{
  var sets := set v | v in graph.0 :: edges(graph,v);
  forall e | e in graph.1 ensures (exists s :: s in sets && e in s)
  {
   assert exists u,v :: u in graph.0 && v in graph.0 && e == {u,v};
   var u,v :|u in graph.0 && v in graph.0 && e == {u,v};
   assert e in edges(graph,u);
  } 

}

lemma VertexCover_SetCover(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (U,S,k'):= VertexCover_to_SetCover(graph,k);
        VertexCover(graph,k) <==> SetCover(U,S,k')
{ 
    VertexCover_SetCover1(graph,k);
    VertexCover_SetCover2(graph,k);
}

lemma cardinal_of_set(graph:Graph, s:set<Node>)
requires isValidGraph(graph)
requires s <= graph.0 
ensures |set v | v in s :: edges(graph,v)| <= |s| 
{ if s == {} {}
  else {
    var o :| o in s;
    cardinal_of_set(graph, s-{o});
    var so := set v | v in s-{o} :: edges(graph,v);
    assert (set v | v in s :: edges(graph,v)) == so + {edges(graph,o)};
    }
}


lemma VertexCover_SetCover1(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (U,S,k'):= VertexCover_to_SetCover(graph,k);
        VertexCover(graph,k) ==> SetCover(U,S,k')
{ var (U,S,k'):= VertexCover_to_SetCover(graph,k);
    if (VertexCover(graph,k)){
    var s:set<Node> :|  s <= graph.0 && isVertexCover(s,graph) && |s| <= k  ;
    var sc := set v | v in s :: edges(graph,v);
    cardinal_of_set(graph,s);
    assert k' <= k;
    forall e | e in U ensures (exists s :: s in sc && e in s)
    {
        var u,v :| u in graph.0 && v in graph.0 && e == {u,v};
        assert u in s || v in s;
        if (u in s) { assert e in edges(graph,u) && edges(graph,u) in sc;}
        else {assert e in edges(graph,v) && edges(graph,v) in sc;}
    }
}

}

lemma VertexCover_SetCover2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (U,S,k'):= VertexCover_to_SetCover(graph,k);
        VertexCover(graph,k) <== SetCover(U,S,k')
