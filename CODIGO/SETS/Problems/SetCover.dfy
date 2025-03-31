include "../Auxiliar/SetFacts.dfy"

//DEFINICION DEL PROBLEMA SET COVER

ghost predicate SetCover<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
{
  exists C:set<set<T>> | C <= S :: isCover(U, C) && |C| <= k
}

ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall u | u in universe :: (exists s | s in sets :: u in s)
}



method verifyIsCover<T>(universe:set<T>, sets:set<set<T>>, k:nat, I:set<set<T>>) returns (b:bool)   
requires forall s | s in sets :: s <= universe
ensures b == (I <= sets && isCover(universe, I) && |I| <= k)
{
  var u := universe;
  var b1:= true;

  while (u != {} && b1)
  invariant u <= universe 
  invariant b1 == isCover(universe-u,I)
  {
   ghost var oldu := u;
   var e1 := pick(u); 
   u := u - {e1};  

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
   assert universe - u == universe - oldu + {e1}; 
  }
  assert b1 ==> u == {} &&  universe-u == universe;
  b := b1 && I <= sets && |I| <= k ;
}
