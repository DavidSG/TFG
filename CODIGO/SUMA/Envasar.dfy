include "Sum.dfy"

// DEFINICION DEL PROBLEMA ENVASAR

// El problema Envasar consiste en dado un vector de enteros A, E y k decidir 
// si es posible dividir los elementos en un número menor o igual que k de subconjuntos disjuntos 
// tales que la suma de los elementos de cada subconjunto sea a lo sumo E
ghost predicate Envasar(A:multiset<int>, E:int, k:int)
{
  exists S:multiset<multiset<int>> | forall e | e in S :: e <= A && Sum(e) <= E :: |S| <= k 
}

