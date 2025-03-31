include "../Auxiliar/SetFacts.dfy"
// DEFINICION DEL PROBLEMA HITTING SET

ghost predicate HittingSet<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat)
  requires forall s | s in sets :: s <= universe // los sets son subsets del universo
{
  exists s:set<T> :: hitsSets(sets, s) && |s| <= cardinality && s <= universe
}

ghost predicate hitsSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}

method checkHittingSet<T>(universe:set<T>, sets:set<set<T>>, k:nat, I:set<T>) returns (b:bool)
  requires forall s | s in sets :: s <= universe
  ensures b == (I <= universe && hitsSets(sets,I) && |I| >= k)
{
  var s := sets;
  var b1:= true;
  
  while (s != {} && b1)
  invariant s <= sets
  invariant b1 == forall s1 | s1 in sets - s :: I * s1 != {}
  {
    var e1 := pick(s); 
    s := s - {e1};

    b1 := b1 && I * e1 != {};
  }
   
  assert b1 == forall s1 | s1 in sets :: I * s1 != {};
  b := b1 && I <= universe && |I| >= k;
}
