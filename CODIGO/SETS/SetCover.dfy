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

method verifyIsCover<T>(universe:set<T>, sets:set<set<T>>, k:nat, witnes:set<set<T>>) returns (b:bool)
ensures b == isCover(universe, witnes) && |witnes| <= k 
