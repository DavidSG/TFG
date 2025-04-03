include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

function ParticionNat_to_ParticionInt(A:multiset<nat>) : (r:(multiset<int>))
{
    (A)
}

lemma ParticionNat_ParticionInt(A:multiset<nat>)
  ensures var PA:= ParticionNat_to_ParticionInt(A);
          ParticionNat(A) <==> ParticionInt(PA)
{ 
    ParticionNat_ParticionInt1(A);
    ParticionNat_ParticionInt2(A);
}

lemma ParticionNat_ParticionInt1(A:multiset<nat>)
    ensures var PA := ParticionNat_to_ParticionInt(A);
          ParticionNat(A) <== ParticionInt(PA)
{   
    var PA := ParticionNat_to_ParticionInt(A);
    if (ParticionInt(PA)) {
        // Se selecciona dos conjuntos IP1, IP2 que resuelva ParticionInt(PA)
        var IP1:multiset<int>,IP2:multiset<int> :| IP1 <= PA && IP2 <= PA && IP1 + IP2 == PA && GSumInt(IP1) == GSumInt(IP2);

        // Se transforma IP1, IP2 en NP1, NP2 (son iguales pero NP1, NP2 son multisets de naturales)
        // Esto es posible ya que todos los enteros de IP1, IP2 deben ser positivos,
        // Porque IP1, IP2 son subconjuntos de PA, que a su vez es equivalente a A que es un multiconjunto de naturales
        var NP1:multiset<nat> := IP1; var NP2:multiset<nat> := IP2; 

        // Demostramos que la suma de un multiconunto de naturales es igual a la suma de un multiconjunto de enteros 
        // si sus elementos son iguales
        GSumPositiveIntNat(NP1); GSumPositiveIntNat(NP2);

        // NP1, NP2 resuelven ParticionNat(A) ya que son subconjuntos de A (que es equivalente a PA) 
        // y su suma es igual por los lemas anteriores 
        assert NP1 <= A && NP2 <= A && NP1 + NP2 == A && GSumNat(NP1) == GSumNat(NP2);
    }
}



lemma ParticionNat_ParticionInt2(A:multiset<nat>)
    ensures var PA := ParticionNat_to_ParticionInt(A);
          ParticionNat(A) ==> ParticionInt(PA)
{
    if (ParticionNat(A)) {
        var PA := ParticionNat_to_ParticionInt(A);
        // Se selecciona dos conjuntos NP1, NP2 que resuelva ParticionInt(PA)
        var NP1:multiset<nat>,NP2:multiset<nat> :| NP1 <= A && NP2 <= A && NP1 + NP2 == A && GSumNat(NP1) == GSumNat(NP2);

        // Se transforma IP1, IP2 en NP1, NP2 (son iguales pero NP1, NP2 son multisets de naturales)
        // Esto es posible ya que todos los naturales son por definición también enteros
        var IP1:multiset<int> := NP1; var IP2:multiset<int> := NP2; 

        // Demostracion: La suma de un multiconunto de naturales es igual a la suma de un multiconjunto de enteros 
        // si sus elementos son iguales
        GSumPositiveIntNat(IP1); GSumPositiveIntNat(IP2);

        // IP1, IP2 resuelven ParticionInt(PA) ya que son subconjuntos de PA (que es equivalente a A) 
        // y su suma es igual por los lemas anteriores
        assert IP1 <= PA && IP2 <= PA && IP1 + IP2 == PA && GSumInt(IP1) == GSumInt(IP2);
    }
}