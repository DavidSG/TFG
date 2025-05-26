include "../Auxiliar/Graph.dfy"
include "../Problems/VertexCover.dfy"
include "../../SETS/Problems/SetCover.dfy"

function edges(graph:Graph,v:nat):set<set<nat>>
    requires isValidGraph(graph)
    requires v in graph.0
{ set e | e in graph.1 && v in e}


lemma without_edges(graph:Graph,v:Node, v':Node)
requires isValidGraph(graph)
requires v in graph.0 && v' in graph.0 && v != v'
ensures edges(graph,v')-{{v,v'}}== edges((graph.0-{v}, graph.1-edges(graph,v)),v')

lemma is_in_edges(graph:Graph, u:Node, v:Node, v':Node)
requires isValidGraph(graph)
requires u in graph.0 && v in graph.0 && {u,v} in graph.1
requires v' in graph.0
requires {u,v} in edges(graph,v')
ensures  u == v' || v == v'
{}

function VertexCover_to_SetCover(graph:Graph, k:int) : (r:(set<set<nat>>,set<set<set<nat>>>,int))
    requires isValidGraph(graph)
    ensures isCover(r.0,r.1)
{ isSetCover(graph);
  if (k < 0) then ({{0,1}},{{{0,1}}},0)//ambos devuelven false
  else (graph.1,set v | v in graph.0 :: edges(graph,v) ,k)
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
    assert SetCover(U,S,k');
}

}
function min(s:set<Node>) : (x:Node)
requires s != {}
ensures x in s && (forall y | y in s :: x <= y)

function minSetsVertex(graph: Graph, v: Node) : (minv:Node)
requires isValidGraph(graph) && v in graph.0
{ var allVs := set v' | v' in graph.0 && edges(graph,v) == edges(graph,v');
  assert v in allVs;
  min(allVs)
}


lemma cardinal_of_setedges(graph: Graph, C:set<set<Edge>>, s:set<Edge>, mins:Node)
requires isValidGraph(graph)
requires C <= (set v | v in graph.0 :: edges(graph,v))  && {} !in C
requires s in C && mins in graph.0 && mins == minSetsVertex(graph,mins) && s == edges(graph,mins)
ensures 
        var C' := (set c | c in C-{s} :: c-edges(graph,mins)) -{{}};
        |C'| <= |C|-|set c | c in C :: c - edges(graph,mins) == {}|
/*{
  if (C-{s} == {}) {}
  else {
    var C' := (set c | c in C-{s} :: c-edges(graph,mins)) -{{}};
    var s':| s' in C-{s};
    assert s' != s && s' !={}; assert s in C-{s'};
    cardinal_of_setedges(graph,C-{s'}, s, mins);
    var C'' := (set c | c in (C-{s'})-{s} :: c-edges(graph,mins)) -{{}};
    assert |C''| <= |(C-{s'})-{s}|;
    assert C'' == (set c | c in (C-{s})-{s'} :: c-edges(graph,mins)) -{{}};
    assert (C-{s})-{s'} + {s'} == C -{s};
    assert s' != edges(graph,mins); 
    if (s'-edges(graph,mins) == {} || s' - edges(graph,mins) in C'') {
      assert C' == C''; 
      assert |C'|==|C''| <= |(C-{s'})-{s}| == |C-{s}|-1 <= |C-{s}|;
    }
    else {
      assert C' == C'' + {s'- edges(graph,mins)};
      assert |C'| == |C''| + 1 <= |(C-{s'})-{s}| + 1 <= |C-{s}|;
    }
  }

}*/


lemma cardinal_of_subset<T>(s1:set<T>,s2:set<T>)
requires s1 <= s2
ensures |s1| <= |s2|




lemma cardinal_of_setCover(graph: Graph, C:set<set<Edge>>, VC:set<Node>)
decreases graph.0,graph.1
requires isValidGraph(graph) //&& graph.1 != {}
requires C <= (set v | v in graph.0 :: edges(graph,v)) 
requires isCover(graph.1, C)  && {} !in C
requires VC == set v | v in graph.0 && edges(graph,v) in C :: minSetsVertex(graph,v)
ensures  |VC| <= |C|
{ if (C== {}) {}
  else{
    var s:| s in C;
    assert  s != {};
    var u,v :| {u,v} in s;
    assert s == edges(graph,u) || s == edges(graph,v);
    var mins;

    /*if (s ==edges(graph,u)) 
      {mins := minSetsVertex(graph,u);}
    else 
       {mins := minSetsVertex(graph,v);}  */
    assume s == edges(graph,u);
    mins := minSetsVertex(graph,u);
    //assert s == edges(graph,mins) == edges(graph,u);
    var graph' := (graph.0-{mins}, graph.1-edges(graph,mins));
    
    var C' := (set c | c in C-{s} :: c-edges(graph,mins)) -{{}};
    assert |C-{s}| == |C| - 1;
    cardinal_of_setedges(graph,C,s,mins); 
    
    
    assert isCover(graph'.1,C') by{
       forall e | e in graph'.1 
       ensures (exists c' | c' in C' :: e in c')
       { var e1,e2 :| e == {e1,e2};
         assert e1 != mins || e2 != mins;
         var c :| c in C && e in c && c != s;
         assert c in C-{s};
         assert e in c-edges(graph,u);
        }
    }
    var VC' := set v | v in graph'.0 && edges(graph',v) in C' :: minSetsVertex(graph',v);
    
    forall z | z in C' ensures z in (set v | v in graph'.0 :: edges(graph',v)){
        var c :| c in C-{s} && z == c-edges(graph,u);
        var v' :| v' in graph.0 && v' != u && c == edges(graph,v');
        assert edges(graph,v')-edges(graph,u) == edges(graph',v');
        
    }
    assert C' <= (set v | v in graph'.0 :: edges(graph',v)); 

    cardinal_of_setCover(graph',C',VC');
    assert mins !in VC' && mins in VC;
    forall v | v in VC ensures v in VC' || (edges(graph,v) in C && edges(graph,v)- edges(graph,mins) == {})
    {
      if (v !in graph'.0) {assert v == mins;}
      else if (v !in VC')
      {
        assert edges(graph',v) !in C' || minSetsVertex(graph',v)!=v;
        if (edges(graph',v) !in C') {
          assert edges(graph',v) == edges(graph,v)- edges(graph,mins);
          assert edges(graph,v)- edges(graph,mins) == {};}
        else {
          var allVs := set v' | v' in graph'.0 && edges(graph',v) == edges(graph',v');
          assume false;}
        assume false; 
      }
    }
  
    assume VC <= VC' + (set v | v in graph.0 && edges(graph,v) in C && edges(graph,v)- edges(graph,mins) == {});
    //assert |VC'| <= |C'| <= |C| - 1; 
    assume false;
  }

}

lemma {:verify true} VertexCover_SetCover2(graph:Graph, k:int)
    requires isValidGraph(graph)
    ensures var (U,S,k'):= VertexCover_to_SetCover(graph,k);
        VertexCover(graph,k) <== SetCover(U,S,k')
{
  var (U,S,k'):= VertexCover_to_SetCover(graph,k);
  if (SetCover(U,S,k'))
  {if (k' == 0) {} 
   else if (graph.1 == {}) { assert isVertexCover({},graph);}
   else{ 
    var C': set<set<Edge>> :| C' <= S && isCover(U, C') && |C'| <= k';
    var C;
    if ({} in C') {C := C' -{{}}; assert isCover(graph.1,C);}
    else { C := C';} 
    var VC := set v | v in graph.0 && edges(graph,v) in C :: minSetsVertex(graph,v); 
    assert VC <= graph.0;
    forall e | e in graph.1 ensures |VC * e| > 0
    {
      var u, v :| e == {u,v};
      var edgesu := edges(graph,u);
      var edgesv := edges(graph,v);
      assert edgesu in C || edgesv in C;
      if (edgesu !in C) 
        {assert v in VC;} 
      if (edgesv !in C)
        {assert u in VC;}
      //Puede suceder que edgesu == edgesv 
      //Por ejemplo una unica arista {u,v}
      // En tal caso uno de los dos es el menor y es el que está en C
    }     
    
    cardinal_of_setCover(graph,C,VC);      
   }
  }


}
