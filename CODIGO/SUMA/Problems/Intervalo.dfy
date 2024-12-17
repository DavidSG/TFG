include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA INTERVALO

// Dado un vector de naturales E, y enteros S y T con S < T escoger un
// subconjunto de valores que sumen una cantidad V que cumpla S <= V < T

ghost predicate Intervalo(A:multiset<nat>, S:nat, T:nat)
{
  exists I:multiset<nat> | I <= A :: S <= GSumNat(I) < T
}

method {:verify true} checkIntervalo(A:multiset<nat>, S:nat, T:nat, I:multiset<nat>) returns (b:bool)
ensures b == (I <= A && S <= GSumNat(I) < T)
{ 
  var suma := mSumaNat(I);
  b := I <= A && S <= suma < T; 
}