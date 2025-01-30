include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

function FMultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0
ensures r == GMultisetNegToPos(A)
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        (multiset{-min} + FMultisetNegToPos(A-multiset{min}))
}

ghost function GMultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0
ensures forall e | e in r :: e > 0 && -e in A
ensures forall e | -e in A :: e in r && r[e] == A[-e]
//ensures forall e | e in A :: -e in r && r[-e] == A[e]//esto se queda colgado
ensures |A| == |r|
{
    if A == multiset{} then multiset{}
    else 
        var m :| m in A; 
        (multiset{-m} + GMultisetNegToPos(A-multiset{m}))
}

function FPositiveElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r == GPositiveElements(A)
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
ensures r == GNegativeElements(A)
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
ensures r <= A 
ensures forall e | e in A && e >= 0 :: e in r && r[e] == A[e]
ensures forall e | e in r :: e >= 0 {  
    if A == multiset{} then multiset{}
    else 
        var m :| m in A;
        if m >= 0 then 
            (multiset{m} + GPositiveElements(A - multiset{m}))
        else
            (GPositiveElements(A - multiset{m}))
}

ghost function GNegativeElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A 
ensures forall e | e in A && e < 0 :: r[e] == A[e]
ensures forall e | e in r :: e < 0
{  
    if A == multiset{} then multiset{}
    else 
        var m :| m in A;
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




lemma FPositiveUnion(P1: multiset<int>, P2: multiset<int>)
    ensures FPositiveElements(P1 + P2) == FPositiveElements(P1) + FPositiveElements(P2)

lemma FNegativeUnion(P1: multiset<int>, P2: multiset<int>)
    ensures FNegativeElements(P1 + P2) == FNegativeElements(P1) + FNegativeElements(P2)

lemma FMultisetNegToPosUnion(P1: multiset<int>, P2: multiset<int>)
     requires forall e | e in P1 :: e < 0
     requires forall e | e in P2 :: e < 0
     ensures FMultisetNegToPos(P1 + P2) == FMultisetNegToPos(P1) + FMultisetNegToPos(P2)


lemma {:verify true} Partes(A:multiset<int>)
    ensures A == GPositiveElements(A) + GNegativeElements(A) 
    ensures GPositiveElements(A) * GNegativeElements(A) == multiset{}
{ }

lemma {:verify false} ParticionInt_ParticionNat1(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) <== ParticionNat(PA)
{   
     Partes(A);
    var PA := ParticionInt_to_ParticionNat(A);
    if (ParticionNat(PA)) {
        var P1:multiset<nat>,P2:multiset<nat> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumNat(P1) == GSumNat(P2);
        
        
        var PAInt:multiset<int> := PA;
        assert PAInt == GPositiveElements(A) + GMultisetNegToPos(GNegativeElements(A));

        var NegativeA:multiset<int> := GMultisetNegToPos(GNegativeElements(A));

        var Intersection:multiset<int> := P1*NegativeA; NegativeA := NegativeA - Intersection;
        var P1Neg := Intersection; var P1Pos := P1 - P1Neg;

        var P2Neg := NegativeA; 
        //var P2Pos := P2 - P2Neg;
        var P2Pos := multiset{};

        var IP1:multiset<nat> := P1Pos + P2Neg; var IP2:multiset<nat> := P2Pos + P1Neg; 

        assume IP1 <= A && IP2 <= A && IP1 + IP2 == A && GSumInt(IP1) == GSumInt(IP2);
    }
}


lemma {:verify false} ParticionInt_ParticionNat2(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) ==> ParticionNat(PA)
{
    if (ParticionInt(A)) {
        Partes(A); 
        var PA:multiset<nat> := ParticionInt_to_ParticionNat(A); var PAInt:multiset<int> := PA;
        
        var P1:multiset<int>,P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);
        Partes(P1); Partes(P2);
        
        var NP1:multiset<int> := GPositiveElements(P1) + GMultisetNegToPos(GNegativeElements(P2)); 
        var NP2:multiset<int> := GPositiveElements(P2) + GMultisetNegToPos(GNegativeElements(P1));

        // Demostracion 1 :
        
        // FALTA POR DEMOSTRAR ALGUNA PROPIEDAD QUE PERMITA INTERCALAR ELEMENTOS COMO Positivos + Negativos = Negativos + Positivos
        //assert PAInt == GPositiveElements(A) + GMultisetNegToPos(GNegativeElements(A));
        
        assert A == P1 + P2;
        assert P1 == GPositiveElements(P1) + GNegativeElements(P1);
        assert P2 == GPositiveElements(P2) + GNegativeElements(P2);
        assert A == GPositiveElements(P1) + GNegativeElements(P1) + P2;
        assume false;
        calc {
            PA;
            FPositiveElements(A) + FMultisetNegToPos(FNegativeElements(A));
            FPositiveElements(P1 + P2) + FMultisetNegToPos(FNegativeElements(P1 + P2));
            { FPositiveUnion(P1,P2); 
              FNegativeUnion(P1,P2);
            }
            FPositiveElements(P1) + FPositiveElements(P2)+
            FMultisetNegToPos(FNegativeElements(P1) + FNegativeElements(P2));
            {   
                FMultisetNegToPosUnion(FNegativeElements(P1),FNegativeElements(P2));
                assume false;
            }
            FPositiveElements(P1) + FPositiveElements(P2) 
            +FMultisetNegToPos(FNegativeElements(P1)) + FMultisetNegToPos(FNegativeElements(P2));
            {
            assume false;
            }
            NP1 + NP2;
            
        }

        //assert GPositiveElements(P2) + GNegativeElements(P2) == GNegativeElements(P2) + GPositiveElements(P2);
        //assert A == P1 + GPositiveElements(P2) + GNegativeElements(P2);
        
        assume GPositiveElements(A) == GPositiveElements(P1) + GPositiveElements(P2);
        
        assume GMultisetNegToPos(GNegativeElements(A)) == GMultisetNegToPos(GNegativeElements(P1)) + GMultisetNegToPos(GNegativeElements(P2));


        //assert NP1 <= PAInt;
        //assert NP2 <= PAInt;
        //assert NP1 <= PAInt && NP2 <= PAInt; 

        
        //assert NP1 == GPositiveElements(P1) + GMultisetNegToPos(GNegativeElements(P2));
        //assert NP2 == GPositiveElements(P2) + GMultisetNegToPos(GNegativeElements(P1));
        //assert NP1 + NP2 == PAInt;

        assert NP1 <= PA && NP2 <= PA;
        assume NP1 + NP2 == PA;
        assume GSumNat(NP1) == GSumNat(NP2);
    }
}