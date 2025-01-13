include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

function abs(num:int) : int
{
    if num >= 0 then num
    else -num
}

function MultisetAbs(A:multiset<int>) : (r:(multiset<nat>)) 
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        var val := abs(min);
        (multiset{val as nat} + MultisetAbs(A-multiset{min}))
}

function ParticionInt_to_ParticionNat(A:multiset<int>) : (r:(multiset<nat>))
{
    (MultisetAbs(A))        
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
        var P1:multiset<int>,P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);

        var P1Positivo:multiset<int> := multiset{}; var P1Negativo:multiset<int> := multiset{};
        var P2Positivo:multiset<int> := multiset{}; var P2Negativo:multiset<int> := multiset{};

        var P1Aux := P1;
        while (P1Aux != multiset{}) {
            var m := minInt(P1Aux); P1Aux := P1Aux - multiset{m};
            if (m >= 0) {
                P1Positivo := P1Positivo + multiset{m};
            }
            else {
                P1Negativo := P1Negativo + multiset{m};
            }
        }

        var P2Aux := P2;
        while (P2Aux != multiset{}) {
            var m := minInt(P2Aux); P2Aux := P2Aux - multiset{m};
            if (m >= 0) {
                P2Positivo := P2Positivo + multiset{m};
            }
            else {
                P2Negativo := P2Negativo + multiset{m};
            }
        }
        
        
        assert P1Positivo < P1;

        var NP1 := P1Positivo + MultisetAbs(P2Negativo); var NP2 := P2Positivo + MultisetAbs(P1Negativo);
        assume NP1 <= PA && NP2 <= PA && NP1 + NP2 == PA && GSumNat(NP1) == GSumNat(NP2);
    }
}