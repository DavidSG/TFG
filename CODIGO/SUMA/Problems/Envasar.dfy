include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA ENVASAR

// El problema Envasar consiste en dado un vector de enteros A, E y k decidir 
// si es posible dividir los elementos en un número menor o igual que k de subconjuntos disjuntos 
// tales que la suma de los elementos de cada subconjunto sea a lo sumo E
ghost predicate Envasar(A:multiset<nat>, E:nat, k:nat)
{
  exists S:multiset<multiset<nat>> | forall e | e in S :: e <= A && GSum(e) <= E :: |S| <= k 
}

