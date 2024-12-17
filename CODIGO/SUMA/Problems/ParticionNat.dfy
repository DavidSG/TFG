include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA PARTICION

// El problema de la Partición de un vector de naturales A[1 n] consiste en decidir si podemos separar
// los elementos del vector en dos partes disjuntas, y cuya union sea A, que sumen lo mismo .
ghost predicate Particion(A:multiset<nat>)
{
  exists P1:multiset<nat>, P2:multiset<nat> | 
    P1 <= A && P2 <= A && P1 + P2 == A :: GSumNat(P1) == GSumNat(P2)
}

method {:verify true} checkParticionNat(A:multiset<nat>, P1:multiset<nat>, P2:multiset<nat>) returns (b:bool)
ensures b ==  (P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2))
{ 
  var suma1 := mSumaNat(P1);
  var suma2 := mSumaNat(P2);
  b := P1 <= A && P2 <= A && P1 + P2 == A && suma1 == suma2; 
}