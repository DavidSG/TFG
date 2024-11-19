include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA PARTICION

// El problema de la Partición de un vector de enteros A[1 n] consiste en decidir si podemos separar
// los elementos del vector en dos partes disjuntas, y cuya union sea A, que sumen lo mismo .
ghost predicate Particion(A:multiset<nat>)
{
  exists P1:multiset<nat>, P2:multiset<nat> | P1 <= A && P2 <= A && P1 * P2 == multiset{} && P1 + P2 == A:: GSum(P1) == GSum(P2)
}
