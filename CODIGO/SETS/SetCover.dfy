//DEFINICION DEL PROBLEMA SET COVER

ghost predicate SetCover<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
{
  exists C:set<set<T>> | C <= S :: isCover(U, C) && |C| <= k
}

ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
requires forall s | s in sets :: s <= universe
{
  forall u | u in universe :: (exists s | s in sets :: u in s)
}

method pick<T>(S:set<T>) returns (r:T)
  requires S != {} //&& |S| > 0
  ensures r in S
{
  var v :| v in S;
  return v;
}

method verifyIsCover<T>(universe:set<T>, sets:set<set<T>>, k:nat, I:set<set<T>>) returns (b:bool)   
requires forall s | s in sets :: s <= universe
ensures b == (I <= sets && isCover(universe, I) && |I| <= k)
{
  var u := universe;
  var b1:= true;
  while (u != {} && b1)
  invariant u <= universe 
  invariant b1 == forall u1 | u1 in universe - u :: (exists s | s in I :: u1 in s)
  {
   var e1 := pick(u); 
   var s := I; var b2:= false;
   while (s != {} && !b2)
     invariant s <= I
     invariant b2 == exists s1 | s1 in I - s :: e1 in s1
   { 
      var e2 := pick(s); 
      b2 := e1 in e2;
      s:= s-{e2};
   }
   b1 := b1 && b2;
   u := u - {e1};  
  }
   
  assert b1 == forall u1 | u1 in universe - u :: (exists s | s in I :: u1 in s);
  b := I <= sets && |I| <= k && b1;
}
