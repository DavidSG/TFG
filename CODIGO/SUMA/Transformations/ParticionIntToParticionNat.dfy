include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

function MultisetAbs(A:multiset<int>) : (r:(multiset<int>)) 
ensures var Positivos:multiset<int> := PositiveElements(A); var Negativos:multiset<int> := NegativeElements(A);
var AbsNegativos:multiset<int> := MultisetNegToPos(Negativos);
Positivos <= A && Negativos <= A && Positivos + Negativos == A && Positivos <= r;
ensures forall e | e in r :: e >= 0;
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        if min >= 0 then (multiset{min} + MultisetAbs(A-multiset{min}))
        else (multiset{-min} + MultisetAbs(A-multiset{min}))
}

function MultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0;
ensures forall e | e in A :: -e in r;
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        (multiset{-min} + MultisetNegToPos(A-multiset{min}))
}

function ParticionInt_to_ParticionNat(A:multiset<int>) : (r:(multiset<nat>))
{   
    var r: multiset<nat> := MultisetAbs(A);
    (r)        
}

lemma ParticionInt_ParticionNat(A:multiset<int>)
  ensures var PA:= ParticionInt_to_ParticionNat(A);
          ParticionInt(A) <==> ParticionNat(PA)
{ 
    ParticionInt_ParticionNat1(A);
    ParticionInt_ParticionNat2(A);
}

ghost function PositiveElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A && forall e | e in r :: e >= 0;
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m >= 0 then 
            (multiset{m} + PositiveElements(A - multiset{m}))
        else
            (PositiveElements(A - multiset{m}))
}

ghost function NegativeElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A && forall e | e in r :: e < 0;
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m < 0 then 
            (multiset{m} + NegativeElements(A - multiset{m}))
        else
            (NegativeElements(A - multiset{m}))
}

lemma ParticionInt_ParticionNat1(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) <== ParticionNat(PA)
{   
    var PA := ParticionInt_to_ParticionNat(A);
    if (ParticionNat(PA)) {
        var P1:multiset<nat>,P2:multiset<nat> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumNat(P1) == GSumNat(P2);

        var ANeg:multiset<nat> := MultisetAbs(NegativeElements(A));
        var P2Neg:multiset<nat> := P1*ANeg; var P1Neg:multiset<nat> := P2*ANeg;

        var IP1:multiset<nat> := P1; var IP2:multiset<nat> := P2; 

        assume IP1 <= A && IP2 <= A && IP1 + IP2 == A && GSumNat(IP1) == GSumNat(IP2);
    }
}


lemma ParticionInt_ParticionNat2(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) ==> ParticionNat(PA)
{
    if (ParticionInt(A)) {
        var PA := ParticionInt_to_ParticionNat(A);
        var P1:multiset<int>,P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);

        var P1Positivo:multiset<int> := PositiveElements(P1); var P1Negativo:multiset<int> := NegativeElements(P1);
        var P2Positivo:multiset<int> := PositiveElements(P2); var P2Negativo:multiset<int> := NegativeElements(P2);        
        
        assert P1Positivo <= P1 && P1Negativo <= P1 && P2Positivo <= P2 && P2Negativo <= P2;
        assert P1Positivo <= A && P1Negativo <= A && P2Positivo <= A && P2Negativo <= A;

        assert PA == MultisetAbs(A);
        assume PA == PositiveElements(A) + MultisetNegToPos(NegativeElements(A));
        assert P1Positivo <= A && P1Positivo <= PositiveElements(A);
        assert P1Positivo <= PA && P2Positivo <= PA;
        //
        assert MultisetNegToPos(P1Negativo) <= PA && MultisetNegToPos(P2Negativo) <= PA;

        var NP1 := P1Positivo + MultisetAbs(P2Negativo); var NP2 := P2Positivo + MultisetAbs(P1Negativo);

        assume NP1 <= PA && NP2 <= PA && NP1 + NP2 == PA && GSumNat(NP1) == GSumNat(NP2);
    }
}