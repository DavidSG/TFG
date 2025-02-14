include "../Auxiliar/Sum.dfy"

// nota: I | **** :: *** -> lo de despues de | significa QUE ES I, y lo de despues de :: significa QUE LIMITACIONES TIENE

// DEFINICION DEL PROBLEMA SUMA
// El problema de la Suma consiste en decidir, dados un vector de enteros A[] y un valor
// S, si podemos encontrar un subconjunto I del conjunto de índices del vector tal que la suma de
// los correspondientes elementos del mismo sea S

ghost predicate SumaInt(A:multiset<int>, S:int)
{
  exists I:multiset<int> | I <= A :: GSumInt(I) == S
}

method {:verify true} checkSumaInt(A:multiset<int>, S:int, I:multiset<int>) returns (b:bool)
ensures b == (I <= A && GSumInt(I) == S)
{ 
  var suma := FSumInt(I);
  FSumIntComputaGSumInt(I);
  //mSumaInt(I);
  b := I <= A && suma == S; 

}
