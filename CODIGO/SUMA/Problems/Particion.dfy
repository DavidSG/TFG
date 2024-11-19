include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA PARTICION

// El problema de la Partición de un vector de enteros A[1 n] consiste en decidir si podemos separar
// los elementos del vector en dos partes disjuntas, y cuya union sea A, que sumen lo mismo .
ghost predicate Particion(A:multiset<int>)
{
  exists P1:multiset<int>, P2:multiset<int> | 
    P1 <= A && P2 <= A && P1 + P2 == A:: GSumInt(P1) == GSumInt(P2)
}
