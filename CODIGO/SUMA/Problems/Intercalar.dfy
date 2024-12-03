include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA INTERCALAR

// Dado un vector de naturales E, decidir si es posible intercalar entre 
// cada dos de ellos los signos + -, de nabera que el valor de la expresión
// resultante evaluada de izquierda a derecha, y sin ningún tipo de precedencia
// entre sus operadores, sea finalmente 0

ghost predicate Intercalar(E:seq<nat>)
{
  if (|E| == 0) then true
  else
   var elements:= multiset(E);
   exists E1,E2 :: 
     E[0] in E1 && E1 <= elements //E1 positive elements
     && E2 <= elements               //E2 negative elements
     && E1 + E2 == elements
     && GSumInt(E1) - GSumInt(E2) == 0
}
