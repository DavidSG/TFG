include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA PARTICION

// El problema de la Partición de un vector de enteros A[1 n] consiste en decidir si podemos separar
// los elementos del vector en dos partes disjuntas, y cuya union sea A, que sumen lo mismo .

ghost predicate ParticionInt(A:multiset<int>)
{
  exists P1:multiset<int>, P2:multiset<int> :: P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2)
}

ghost predicate IsPartitionInt(A:multiset<int>,P1:multiset<int>,P2:multiset<int>)
{ P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2) }

lemma existsPartition(A:multiset<int>,P1:multiset<int>,P2:multiset<int>)
requires IsPartitionInt(A,P1,P2)
ensures ParticionInt(A)
{}

method {:verify true} checkParticionInt(A:multiset<int>, P1:multiset<int>, P2:multiset<int>) returns (b:bool)
ensures b ==  (P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2))
{ 
  var suma1 := mSumaInt(P1);
  var suma2 := mSumaInt(P2);
  b := P1 <= A && P2 <= A && P1 + P2 == A && suma1 == suma2; 
}