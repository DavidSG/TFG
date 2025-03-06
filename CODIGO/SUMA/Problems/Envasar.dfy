include "../Auxiliar/Sum.dfy"

// DEFINICION DEL PROBLEMA ENVASAR

// El problema Envasar consiste en dado un vector de enteros A, E y k decidir 
// si es posible dividir los elementos en un número menor o igual que k de subconjuntos disjuntos 
// tales que la suma de los elementos de cada subconjunto sea a lo sumo E
ghost predicate Envasar(A:multiset<nat>, E:nat, k:nat)
{ 
  exists I:multiset<multiset<nat>> :: 
   && |I| <= k 
   && Union(I) == A
   && forall e | e in I :: (e <= A && GSumNat(e) <= E)
    
}


function minMultiset (m:multiset<multiset<nat>>): (l:multiset<nat>)
requires m != multiset{}
ensures l in m && (forall x | x in m :: GSumNat(l) <= GSumNat(l)) 

// UNION

ghost function Union (I:multiset<multiset<nat>>) : multiset<nat>
{
  if I == multiset{} then multiset{}
  else var i :| i in I; i + Union(I-multiset{i})
}

/*
function FUnion (I:multiset<multiset<nat>>) : multiset<nat>
{
  if I == multiset{} then multiset{}
  else var i := minMultiset(I); i + FUnion(I-multiset{i})
}

lemma {:induction m} GUnionPartes(m : multiset<multiset<nat>>, x : multiset<nat>)
ensures GUnion(m) == x + GUnion(m - multiset{x})


lemma {:induction m} FUnionComputaGUnion(m : multiset<multiset<nat>>)
ensures FUnion(m) == GUnion(m)
{ 
  if m == multiset{} {
    assert FUnion(m) == GUnion(m);
  }
  else {
    var x :| x in m;
    FUnionComputaGUnion(m - multiset{x});
    assert FUnion(m - multiset{x}) == GUnion(m-multiset{x});

    assume FUnion(m) == x + FUnion(m-multiset{x});
    assume x + FUnion(m) == x + GUnion(m - multiset{x});
    assume FUnion(m) == GUnion(m);
  }
}
*/

// VERIFICACION
/*
method {:verify true} checkEnvasar(A:multiset<nat>, E:nat, k:nat, I:multiset<multiset<nat>>) returns (b:bool)
ensures b ==  (|I| <= k 
             && GUnion(I) == A )
             //&& forall e | e in I :: e <= A && GSumNat(e) <= E )
{
  FUnionComputaGUnion(I);
  b := |I| <= k && FUnion(I) == A;
}*/
