ghost function Sum(m : multiset<int>) : int
{
	if m == multiset{} then 0 
  else var x :| x in m; x + Sum(m - multiset{x})
}

// El problema de la Suma consiste en decidir, dados un vector de enteros A[] y un valor
// S, si podemos encontrar un subconjunto I del conjunto de índices del vector tal que la suma de
// los correspondientes elementos del mismo sea S
ghost predicate SumaS(A:multiset<int>, S:int)
{
  exists I:multiset<int> | I <= A :: Sum(I) == S
}

// El problema de la Partición de un vector de enteros A[1 n] consiste en decidir si podemos separar
// los elementos del vector en dos partes disjuntas que sumen lo mismo.
ghost predicate Particion(A:multiset<int>)
{
  exists P1:multiset<int>, P2:multiset<int> | P1 <= A && P2 <= A && P1 * P2 == multiset{} :: Sum(P1) == Sum(P2)
}

// El problema Envasar consiste en dado un vector de enteros A, E y k decidir 
// si es posible dividir los elementos en un número menor o igual que k de subconjuntos disjuntos 
// tales que la suma de los elementos de cada subconjunto sea a lo sumo E
ghost predicate Envasar(A:multiset<int>, E:int, k:int)
{
  exists S:multiset<multiset<int>> | forall e | e in S :: e <= A && Sum(e) <= E :: |S| <= k 
}
