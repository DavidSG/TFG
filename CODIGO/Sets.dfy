ghost predicate SetCover<T>(U:set<T>, S: set<set<T>>, k:int)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
{
  exists C:set<set<T>> | C <= S :: isCover(U, C) && |C| <= k
}

ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall e | e in universe :: (exists s | s in sets :: e in s)
}


// Hitting Set
ghost predicate HittingSet<T>(universe:set<T>, sets:set<set<T>>, cardinality:int)
  requires forall s | s in sets :: s <= universe // los sets son subsets del universo
  //requires forall s1 | s1 in sets :: !(exists s2 | s2 in sets - {s1} :: s1 == s2) // no hay dos sets iguales en S
{
  exists s:set<T> :: hitsSets(sets, s) && |s| <= cardinality && s <= universe
}

ghost predicate hitsSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}


function SetCover_to_HittingSet<T>(U: set<T>, S: set<set<T>>, k: int) : (r:(set<set<T>>, set<set<set<T>>>, int))
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
  ensures forall s | s in r.1 :: s <= r.0 // los sets son subsets del universo
  //ensures forall s1 | s1 in r.1 :: !(exists s2 :: s2 in r.1 && s2 != s1 && s1 == s2) // no hay dos sets iguales en S
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  (S-{{}}, newS, k)
}


lemma {:axiom} SetCover_HittingSet1<T>(U:set<T>, S: set<set<T>>, k:int)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) ==> HittingSet(HU,HS,Hk)
  
 lemma {:axiom} SetCover_HittingSet2<T>(U:set<T>, S: set<set<T>>, k:int)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) <== HittingSet(HU,HS,Hk)

 
lemma {:axiom} SetCover_HittingSet<T>(U:set<T>, S: set<set<T>>, k:int)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (U2, S2, k2) := SetCover_to_HittingSet(U,S,k); SetCover(U,S,k) <==> HittingSet(U2,S2,k2)
  

function HittingSet_to_SetCover<T>(U: set<T>, S: set<set<T>>, k: int) : (r:(set<set<T>>, set<set<set<T>>>, int))
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  //requires forall s1 | s1 in S :: !(exists s2 | s2 in S - {s1} :: s1 == s2) // no hay dos sets iguales en S
  ensures forall s | s in r.1 :: s <= r.0 // los sets son subsets del universo
  ensures isCover(r.0, r.1) // existe un subconjunto de sets tal que su union es igual al universo
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  tisCover(U,S);
  (S-{{}}, newS, k)
}


lemma {:axiom} HittingSet_SetCover1<T>(U:set<T>, S: set<set<T>>, k:int)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  //requires forall s1 | s1 in S :: !(exists s2 | s2 in S - {s1} :: s1 == s2) // no hay dos sets iguales en S
  ensures var (SU,SS,Sk) := HittingSet_to_SetCover(U,S,k);
          HittingSet(U,S,k) ==> SetCover(SU,SS,Sk)
         

lemma {:axiom} HittingSet_SetCover2<T>(U:set<T>, S: set<set<T>>, k:int)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires forall s1 | s1 in S :: !(exists s2 | s2 in S - {s1} :: s1 == s2) // no hay dos sets iguales en S
  ensures var (U2, S2, k2) := HittingSet_to_SetCover(U,S,k); 
          HittingSet(U,S,k) <==> SetCover(U2,S2,k2)
  

//Lo mismo en sentido contrario

/* 
ghost function Sum(a:seq<int>,si : set<int>) : int
requires forall i | i in si :: 0 <= i < |a|
{
	if si == {} then 0 
  else var x :| x in si; a[x] + Sum(a,si - {x})
}

ghost function SumM(m : multiset<int>) : int
{
	if m == multiset{} then 0 
  else var x :| x in m; x + SumM(m - multiset{x})
}

*/

/*method Main() {
  print "Hello, Dafny!\n";
  var U: set<int> := {1,2,3,4,5};
  var S: set<set<int>> := {{1,2,3},{2,4},{3,4},{4,5}};
  var k := 2;

  //var (U2, S2, k2) := SetCover_to_HittingSet(U, S, k);
  //var newS: set<set<int>> := { s | s in S && u in s };
  var newS: set<set<set<int>>> := (set u | u in U :: (set s | s in S && u in s)); 
  
  // Print the result
  print "Grouped sets by elements from U:\n";
  print "newS: ", newS, "\n";
}*/
