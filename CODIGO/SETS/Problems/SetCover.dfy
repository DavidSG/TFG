include "../Auxiliar/SetFacts.dfy"

//DEFINICION DEL PROBLEMA SET COVER

ghost predicate SetCover<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U // los S son subS del universo
  requires isCover(U, S) // existe un subconjunto de S tal que su union es igual al universo
{
  exists I:set<set<T>> | I <= S && |I| <= k :: isCover(U, I)
}

ghost predicate isCover<T>(U:set<T>, I:set<set<T>>)
{
  forall u | u in U :: (exists s | s in I :: u in s)
}



method verifyIsCover<T>(U:set<T>, S:set<set<T>>, k:nat, I:set<set<T>>) returns (b:bool)   
requires forall s | s in S :: s <= U
ensures b == (I <= S && isCover(U, I) && |I| <= k)
{
  var u := U;
  var b1:= true;

  while (u != {} && b1)
  invariant u <= U 
  invariant b1 == isCover(U-u,I)
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
   assert U - u == U - oldu + {e1}; 
  }
  assert b1 ==> u == {} &&  U-u == U;
  b := b1 && I <= S && |I| <= k ;
}
