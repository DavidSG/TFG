include "SetCover.dfy"
include "HittingSet.dfy"

lemma tisCover<T>(U: set<T>, S: set<set<T>>) 
requires forall s | s in S :: s <= U
 ensures 
   var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
   isCover(S-{{}},newS)
{ var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  forall e | e in S-{{}} ensures (exists s | s in newS :: e in s)
  {    assert e != {};
       assert exists n :: n in e; 
       var n :| n in e;
    assume {:axiom} false;
    }
    
}

function HittingSet_to_SetCover<T>(U: set<T>, S: set<set<T>>, k: nat) : (r:(set<set<T>>, set<set<set<T>>>, int))
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures forall s | s in r.1 :: s <= r.0 // los sets son subsets del universo
  ensures isCover(r.0, r.1) // existe un subconjunto de sets tal que su union es igual al universo
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  tisCover(U,S);
  (S-{{}}, newS, k)
}

lemma HittingSet_SetCover<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (SU,SS,Sk) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) <==> SetCover(SU,SS,Sk)
  { var (SU,SS,Sk) := HittingSet_to_SetCover(U,S,k);
    HittingSet_SetCover1(U,S,k);
    HittingSet_SetCover2(U,S,k);
  }

// Demostrar que 
lemma {:axiom} HittingSet_SetCover1<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) ==> SetCover(US,SS,kS)
{
  // if hitting set -> true
  if (HittingSet(U,S,k)) {
    var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
    var C:set<T> :| hitsSets(S, C) && |C| <= k && C <= U;      // {2,4}
    var CS := (set x | x in C :: (set y | y in US && x in y)); // { {{1,2,3},{2,4}}, {{2,4},{3,4},{4,5}} }
 
    
    forall us | us in US
    ensures exists ss :: ss in CS && us in ss
    {
      var sss := (set ss | ss in SS && us in ss); // para {1,2,3} { {{1,2,3} }
      assert sss * CS != {}; // la interseccion de { {{1,2,3} } y { {{1,2,3},{2,4}}, {{2,4},{3,4},{4,5}} }
      var ss :| ss in sss * CS; // s es el elemento elegido de U para hacer el hitting set
      assert us in ss; // u está en S
    }
  }
}

         

lemma {:axiom} HittingSet_SetCover2<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) <== SetCover(US,SS,kS)
{
  var (US,SS,kS) := HittingSet_to_SetCover(U,S,k);
  if (SetCover(US,SS,kS)) {
    var C:set<set<set<T>>> :| C <= SS && isCover(US, C) && |C| <= kS; // { {{1,2,3},{2,4}}, {{2,4},{3,4},{4,5}} }
    var CS:set<T> := (set u | u in U && (set s | s in S && u in s) in C :: u); // {2, 4}

    assert CS != {};

    forall s | s in S
    ensures CS * s != {}
    {
      var cs :| cs in CS;
      assert cs in CS * s;
      assert s * CS != {};
    }
    
  }
}


