include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA SUMA
// El problema de la Suma consiste en decidir, dados un vector de enteros A[] y un valor
// S, si podemos encontrar un subconjunto I del conjunto de índices del vector tal que la suma de
// los correspondientes elementos del mismo sea S

ghost predicate Suma(A:multiset<nat>, S:nat)
{
  exists I:multiset<nat> | I <= A :: GSumNat(I) == S
}