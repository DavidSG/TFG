include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

function FMultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0;
ensures forall e | e in A :: -e in r;
ensures forall e | e in r :: e >= 0;
ensures |A| == |r|;
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        (multiset{-min} + FMultisetNegToPos(A-multiset{min}))
}

function GMultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0;
ensures forall e | e in A :: -e in r;
ensures forall e | e in r :: e >= 0;
ensures |A| == |r|;
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        (multiset{-min} + GMultisetNegToPos(A-multiset{min}))
}

function FPositiveElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A && forall e | e in r :: e >= 0;
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m >= 0 then 
            (multiset{m} + FPositiveElements(A - multiset{m}))
        else
            (FPositiveElements(A - multiset{m}))
}

function FNegativeElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A && forall e | e in r :: e < 0;
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m < 0 then 
            (multiset{m} + FNegativeElements(A - multiset{m}))
        else
            (FNegativeElements(A - multiset{m}))
}

ghost function GPositiveElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A && forall e | e in r :: e >= 0;
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m >= 0 then 
            (multiset{m} + GPositiveElements(A - multiset{m}))
        else
            (GPositiveElements(A - multiset{m}))
}

ghost function GNegativeElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A && forall e | e in r :: e < 0;
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m < 0 then 
            (multiset{m} + GNegativeElements(A - multiset{m}))
        else
            (GNegativeElements(A - multiset{m}))
}

function ParticionInt_to_ParticionNat(A:multiset<int>) : (r:(multiset<nat>))
{   
    (FPositiveElements(A) + FMultisetNegToPos(FNegativeElements(A)))        
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
        var P1:multiset<nat>,P2:multiset<nat> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumNat(P1) == GSumNat(P2);

        var IP1:multiset<nat> := multiset{}; var IP2:multiset<nat> := multiset{}; 

        assume IP1 <= A && IP2 <= A && IP1 + IP2 == A && GSumInt(IP1) == GSumInt(IP2);
    }
}


lemma ParticionInt_ParticionNat2(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) ==> ParticionNat(PA)
{
    if (ParticionInt(A)) {
        var PA:multiset<nat> := ParticionInt_to_ParticionNat(A); var PAInt:multiset<int> := PA;
        var P1:multiset<int>,P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);
        
        var NP1:multiset<int> := GPositiveElements(P1) + GMultisetNegToPos(GNegativeElements(P2)); 
        var NP2:multiset<int> := GPositiveElements(P2) + GMultisetNegToPos(GNegativeElements(P1));

        // Demostracion 1 :
        //assume FPositiveElements(A) == GPositiveElements(A);
        assert PA == FPositiveElements(A) + FMultisetNegToPos(FNegativeElements(A));
        //assert PA == GPositiveElements(A) + FMultisetNegToPos(FNegativeElements(A));
        assume PAInt == GPositiveElements(A) + GMultisetNegToPos(GNegativeElements(A));

        assume GPositiveElements(A) == GPositiveElements(P1) + GPositiveElements(P2);
        assume GMultisetNegToPos(GNegativeElements(A)) == GMultisetNegToPos(GNegativeElements(P1)) + GMultisetNegToPos(GNegativeElements(P2));

        assume GPositiveElements(A) * GNegativeElements(A) == multiset{};

        assert NP1 <= PAInt;
        assert NP2 <= PAInt;
        assert NP1 <= PAInt && NP2 <= PAInt; 

        
        assert NP1 == GPositiveElements(P1) + GMultisetNegToPos(GNegativeElements(P2));
        assert NP2 == GPositiveElements(P2) + GMultisetNegToPos(GNegativeElements(P1));
        //assert NP1 + NP2 == PAInt;

        

        assume NP1 <= PA && NP2 <= PA && NP1 + NP2 == PA && GSumNat(NP1) == GSumNat(NP2);
    }
}