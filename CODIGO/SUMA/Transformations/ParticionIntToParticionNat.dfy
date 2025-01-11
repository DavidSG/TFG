include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

function abs(num:int) : int
{
    if num >= 0 then num
    else -num
}

function ParticionInt_to_ParticionNat(A:multiset<int>) : (r:(multiset<nat>))
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        var val := abs(min);
        (multiset{val as nat} + ParticionInt_to_ParticionNat(A-multiset{min}))
        
}

lemma ParticionInt_ParticionNat(A:multiset<int>)
  ensures var PA:= ParticionInt_to_ParticionNat(A);
          ParticionInt(A) <==> ParticionNat(PA)
{ 
    ParticionInt_ParticionNat1(A);
    ParticionInt_ParticionNat2(A);
}

lemma ParticionInt_ParticionNat1(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) <== ParticionNat(PA)
{   
    var PA := ParticionInt_to_ParticionNat(A);
    if (ParticionNat(PA)) {
        var IP1:multiset<int>,IP2:multiset<int> :| IP1 <= PA && IP2 <= PA && IP1 + IP2 == PA && GSumNat(IP1) == GSumInt(IP2);

        var NP1:multiset<nat> := IP1; var NP2:multiset<nat> := IP2; 

        // Demostracion 1: La suma de un multiconunto de naturales es igual a la suma de un multiconjunto de enteros 
        // si sus elementos son iguales
        SumNatEqualsSumInt(NP1,IP1); SumNatEqualsSumInt(NP2,IP2);
        assert NP1 <= A && NP2 <= A && NP1 + NP2 == A && GSumNat(NP1) == GSumNat(NP2);
    }
}

lemma ParticionInt_ParticionNat2(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) ==> ParticionNat(PA)
{
    if (ParticionInt(A)) {
        var PA := ParticionInt_to_ParticionNat(A);
        var P1:multiset<nat>,P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);

        var (NP1, NP2) := func

        
        assert IP1 <= PA && IP2 <= PA && IP1 + IP2 == PA && GSumInt(IP1) == GSumInt(IP2);
    }
}