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

lemma {:axiom} HittingSet_SetCover1<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (SU,SS,Sk) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) ==> SetCover(SU,SS,Sk)
         

lemma {:axiom} HittingSet_SetCover2<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  ensures var (SU,SS,Sk) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) <== SetCover(SU,SS,Sk)



