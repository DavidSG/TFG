include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA ENVASAR

// El problema Envasar consiste en dado un vector de enteros A, E y k decidir 
// si es posible dividir los elementos en un número menor o igual que k de subconjuntos disjuntos 
// tales que la suma de los elementos de cada subconjunto sea a lo sumo E
ghost predicate Envasar(A:multiset<nat>, E:nat, k:nat)
{ 
  exists I:multiset<multiset<nat>> | Valid(I,A,E) :: |I| <= k;
}

/*exists I:multiset<multiset<nat>> | forall e1 | e1 in I :: e1 <= A && GSum(e1) <= E && forall e2 | e2 in I :: e1 * e2 == multiset{}) 
  :: |I| <= k && Union(I) == A;*/

ghost predicate Valid (I:multiset<multiset<nat>>, A:multiset<nat>, E:nat) : a
{
  if m == multiset{} then {}
  else var i :| i in I; i + Union(m - multiset{i})
}

ghost predicate Union (I:multiset<multiset<nat>>) : multiset<nat>
{
  if m == multiset{} then {}
  else var i :| i in I; i + Union(m - multiset{i})
}
