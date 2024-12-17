include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA SUMA
// El problema de la Suma consiste en decidir, dados un vector de enteros A[] y un valor
// S, si podemos encontrar un subconjunto I del conjunto de índices del vector tal que la suma de
// los correspondientes elementos del mismo sea S

ghost predicate SumaNat(A:multiset<nat>, S:nat)
{
  exists I:multiset<nat> | I <= A :: GSumNat(I) == S
}

method {:verify true} checkSumaNat(A:multiset<nat>, S:nat, I:multiset<nat>) returns (b:bool)
ensures b == (I <= A && GSumNat(I) == S)
{ 
  var suma := mSumaNat(I);
  assert suma == GSumNat(I); 
  b := I <= A && suma == S; 
}