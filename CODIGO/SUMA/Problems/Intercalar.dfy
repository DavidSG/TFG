include "Sum.dfy"

// DEFINICION DEL PROBLEMA INTERCALAR

// Dado un vector de naturales E, decidir si es posible intercalar entre 
// cada dos de ellos los signos + -, de nabera que el valor de la expresión
// resultante evaluada de izquierda a derecha, y sin ningún tipo de precedencia
// entre sus operadores, sea finalmente 0

ghost predicate Intercalar(E:seq<int>)
{
  if |E| == 0 then true
  else
    var En := multiset(E);
    var M := En - multiset{E[0]};

    exists I:multiset<int> | I <= En :: Sum(M) + E[0] == 0 
}
