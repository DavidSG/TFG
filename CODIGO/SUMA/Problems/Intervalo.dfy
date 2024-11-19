include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA INTERVALO

// Dado un vector de naturales E, y enteros S y T con S < T escoger un
// subconjunto de valores que sumen una cantidad V que cumpla S <= V < T

ghost predicate Intervalo(A:multiset<nat>, S:nat, T:nat)
{
  exists I:multiset<int> | I <= A :: S <= GSumInt(I) < T
}
