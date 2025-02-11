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
        var IP1:multiset<int>,IP2:multiset<int> :| IP1 <= PA && IP2 <= PA && IP1 + IP2 == PA && GSumInt(IP1) == GSumInt(IP2);

        var NP1:multiset<nat> := IP1; var NP2:multiset<nat> := IP2; 

        // Demostracion: La suma de un multiconunto de naturales es igual a la suma de un multiconjunto de enteros 
        // si sus elementos son iguales
        GSumPositiveIntNat(NP1);GSumPositiveIntNat(NP2);
        assert NP1 <= A && NP2 <= A && NP1 + NP2 == A && GSumNat(NP1) == GSumNat(NP2);
    }
}

lemma ParticionNat_ParticionInt2(A:multiset<nat>)
    ensures var PA := ParticionNat_to_ParticionInt(A);
          ParticionNat(A) ==> ParticionInt(PA)
{
    if (ParticionNat(A)) {
        var PA := ParticionNat_to_ParticionInt(A);
        var NP1:multiset<nat>,NP2:multiset<nat> :| NP1 <= A && NP2 <= A && NP1 + NP2 == A && GSumNat(NP1) == GSumNat(NP2);

        var IP1:multiset<int> := NP1; var IP2:multiset<int> := NP2; 

        // Demostracion: La suma de un multiconunto de naturales es igual a la suma de un multiconjunto de enteros 
        // si sus elementos son iguales
        GSumPositiveIntNat(IP1); GSumPositiveIntNat(IP2);

        assert IP1 <= PA && IP2 <= PA && IP1 + IP2 == PA && GSumInt(IP1) == GSumInt(IP2);
        existsPartition(PA,IP1,IP2);
        assert ParticionInt(PA);
    }
}