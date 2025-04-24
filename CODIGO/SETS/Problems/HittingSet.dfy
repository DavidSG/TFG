include "../Auxiliar/SetFacts.dfy"
// DEFINICION DEL PROBLEMA HITTING SET

ghost predicate HittingSet<T>(U:set<T>, S:set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U 
{
  exists I:set<T> | I <= U && |I| <= k :: hitsSets(S, I)
}

ghost predicate hitsSets<T>(S:set<set<T>>, I:set<T>)
{
  forall s | s in S :: s * I != {}
}

method checkHittingSet<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<T>) returns (b:bool)
  requires forall s | s in S :: s <= U
  ensures b == (I <= U && hitsSets(S,I) && |I| >= k)
{
  var s := S;
  var b1:= true;
  
  while (s != {} && b1)
  invariant s <= S
  invariant b1 == forall s1 | s1 in S - s :: I * s1 != {}
  {
    var e1 := pick(s); 
    s := s - {e1};

    b1 := b1 && I * e1 != {};
  }
   
  assert b1 == forall s1 | s1 in S :: I * s1 != {};
  b := b1 && I <= U && |I| >= k;
}
