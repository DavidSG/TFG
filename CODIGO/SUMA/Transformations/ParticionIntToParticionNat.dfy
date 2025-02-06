include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

ghost function GMultisetPosToNeg(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e > -1
ensures forall e | e in r :: e < 1 && -e in A
//ensures forall e | e in A :: -e in r && r[-e] == A[e]
ensures forall e | -e in A :: e in r && r[e] == A[-e]
ensures |A| == |r|
{
    if A == multiset{} then multiset{}
    else 
        var m :| m in A; 
        (multiset{-m} + GMultisetPosToNeg(A-multiset{m}))
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

function FMultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0
ensures r == GMultisetNegToPos(A)
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        (multiset{-min} + FMultisetNegToPos(A-multiset{min}))
}



ghost function GPositiveElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A 
ensures forall e | e in A && e >= 0 :: e in r && r[e] == A[e]
ensures forall e | e in r :: e >= 0 
{  
    if A == multiset{} then multiset{}
    else 
        var m :| m in A;
        if m >= 0 then 
            (multiset{m} + GPositiveElements(A - multiset{m}))
        else
            (GPositiveElements(A - multiset{m}))
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

lemma CommutativeUnion<T>(x:multiset<T>,y:multiset<T>)
ensures x + y == y + x
{}
lemma AssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures x + (y + z) == (x + y) + z
{}

lemma CommutativeAssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
ensures (x + y) + (z + u) == (x + u) + (y + z)
{} 

lemma IntersectionUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
//requires (x + y) * z >=  x * y + y * z
//ensures (x + y) * z <= (x * y + y * z)

lemma GPositiveUnion(P1: multiset<int>, P2: multiset<int>)
    ensures GPositiveElements(P1 + P2) == GPositiveElements(P1) + GPositiveElements(P2)

lemma GNegativeUnion(P1: multiset<int>, P2: multiset<int>)
    ensures GNegativeElements(P1 + P2) == GNegativeElements(P1) + GNegativeElements(P2)

lemma GMultisetNegToPosUnion(P1: multiset<int>, P2: multiset<int>)
     requires forall e | e in P1 :: e < 0
     requires forall e | e in P2 :: e < 0
     ensures GMultisetNegToPos(P1 + P2) == GMultisetNegToPos(P1) + GMultisetNegToPos(P2)

lemma GMultisetNegToPosToNeg(A: multiset<int>)
requires forall e | e in A :: e < 0
ensures GMultisetPosToNeg(GMultisetNegToPos(A)) == A


lemma NegSumGMultisetNegToPos(A:multiset<int>)
requires forall e | e in A :: e < 0
ensures GSumNat(GMultisetNegToPos(A)) == - GSumInt(A)

lemma SumGPositiveNegativeElements(A:multiset<int>)
ensures GSumNat(GPositiveElements(A)) == GSumInt(GPositiveElements(A))
ensures GSumNat(GMultisetNegToPos(GNegativeElements(A))) == -GSumInt(GNegativeElements(A))


lemma {:verify true} Partes(A:multiset<int>)
    ensures A == GPositiveElements(A) + GNegativeElements(A) 
    ensures GPositiveElements(A) * GNegativeElements(A) == multiset{}
{ }

lemma IntersectionContained<T>(A: multiset<T>,B:multiset<T>)
ensures A * B <= A && A * B <= B
{}

lemma {:verify true} ParticionInt_ParticionNat1(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) <== ParticionNat(PA)
{   
     Partes(A);
    var PA := ParticionInt_to_ParticionNat(A);
    if (ParticionNat(PA)) {
        var P1:multiset<nat>,P2:multiset<nat> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumNat(P1) == GSumNat(P2);

        /*var PositiveA:multiset<nat> := GPositiveElements(A);
        var NegativeA:multiset<nat> := GMultisetNegToPos(GNegativeElements(A));
        var P1Pos := P1 * PositiveA; var P2Pos := P2 * PositiveA;
        IntersectionContained(P1,PositiveA); IntersectionContained(P2,PositiveA);
        assert P1Pos <= PositiveA <= A; assert P2Pos <= PositiveA <= A;

        var P1Neg := P1 - P1Pos; 
        var P2Neg := P2 - P2Pos; 
        var IP1:multiset<int> := P1Pos + P2Neg; 
        var IP2:multiset<int> := P2Pos + P1Neg; 
         
        assume false;
        //assume IP1 <= A && IP2 <= A && IP1 + IP2 == A && GSumInt(IP1) == GSumInt(IP2);
        */
        Partes(A);
        ghost var AP := GPositiveElements(A);
        ghost var AN := GNegativeElements(A);
        ghost var ANP:= GMultisetNegToPos(AN);
        assert A == AP + AN;
        assert PA == AP + ANP;
        ghost var P1P:multiset<int> := P1 * AP;
        ghost var P2P:multiset<int> := P2 * AP;
        ghost var P1NP:multiset<int> := P1 - P1P;
        ghost var P2NP:multiset<int> := P2 - P2P;
        ghost var P1N:multiset<int> := GMultisetPosToNeg(P1NP);
        ghost var P2N:multiset<int> := GMultisetPosToNeg(P2NP);
        ghost var IP1:multiset<int> := P1P + P2N; 
        ghost var IP2:multiset<int> := P2P + P1N;

        assert P1 + P2 == AP + GMultisetNegToPos(AN);
        assume AP == P1P + P2P;
        assume AN == P2N + P1N;

        calc{
           A;
           AP + AN;
           {assume AP == P1P + P2P;
            assume AN == P2N + P1N;
           }
           (P1P + P2P) + (P2N + P1N);
           {assume false; CommutativeAssociativeUnion<int>(P1P,P2P,P2N,P1N);}
           (P1P + P2N) + (P2P + P1N);
           IP1 + IP2;

        }
        assume false;
        assume A == IP1 + IP2;
        assert IP1 <= A && IP2 <= A;
        assume GSumInt(IP1) == GSumInt(IP2);

         
    }
}


lemma {:verify false} ParticionInt_ParticionNat2(A:multiset<int>)
    ensures var PA := ParticionInt_to_ParticionNat(A);
          ParticionInt(A) ==> ParticionNat(PA)
{
    if (ParticionInt(A)) {
        //Partes(A); 
        var PA:multiset<nat> := ParticionInt_to_ParticionNat(A);         
        var P1:multiset<int>,P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);
        
        
        ghost var P1P := GPositiveElements(P1);
        ghost var P1N := GNegativeElements(P1);
        ghost var P2P := GPositiveElements(P2);
        ghost var P2N := GNegativeElements(P2);
        ghost var P1NP := GMultisetNegToPos(P1N);
        ghost var P2NP := GMultisetNegToPos(P2N);

        Partes(P1); Partes(P2);
        assert P1 == P1P + P1N;
        assert P2 == P2P + P2N;
        GSumIntPartes(P1,P1P,P1N); GSumIntPartes(P2,P2P,P2N);
        assert GSumInt(P1P) +  GSumInt(P1N) == GSumInt(P2P) + GSumInt(P2N);
        assert GSumInt(P1P) - GSumInt(P2N) == GSumInt(P2P) - GSumInt(P1N);
    
        ghost var NP1:multiset<int> := GPositiveElements(P1) + GMultisetNegToPos(GNegativeElements(P2)); 
        ghost var NP2:multiset<int> := GPositiveElements(P2) + GMultisetNegToPos(GNegativeElements(P1));
        // Demostracion:    
        
        //Demostracion de que NP1 y NP2 es una particion de PA
       assert NP1 + NP2 == PA by{   
        calc {
            PA;
            FPositiveElements(A) + FMultisetNegToPos(FNegativeElements(A));
            //{ assert A == P1 + P2;}
            GPositiveElements(P1 + P2) + GMultisetNegToPos(GNegativeElements(P1 + P2));
            { GPositiveUnion(P1,P2); 
              GNegativeUnion(P1,P2);
              GMultisetNegToPosUnion(P1N,P2N);
            }
            (P1P + P2P) 
            + 
            (P1NP + P2NP);        
            {CommutativeAssociativeUnion(P1P, P2P, P1NP,P2NP);}
            (P1P + P2NP)
            +
            (P2P + P1NP);     
            NP1 + NP2;           
        }
       }
       assert NP1 <= PA && NP2 <= PA;
       assert GSumNat(NP1) == GSumNat(NP2)by{
            calc{
                GSumNat(NP1);
                { GSumNatPartes(NP1,P1P,P2NP); }
                GSumNat(P1P)+GSumNat(P2NP);
                {
                    SumGPositiveNegativeElements(P2);
                    SumGPositiveNegativeElements(P1);
                    assert GSumNat(P1P) == GSumInt(P1P);
                    assert GSumNat(P2NP) == -GSumInt(P2N);
                }
                GSumInt(P1P) + (- GSumInt(P2N));
                GSumInt(P2P) + (-GSumInt(P1N));
                {   SumGPositiveNegativeElements(P2);
                    SumGPositiveNegativeElements(P1);
                    assert GSumNat(P2P) == GSumInt(P2P);
                    assert GSumNat(P1NP) == -GSumInt(P1N);}
                GSumNat(P2P) + GSumNat(P1NP);    
                {GSumNatPartes(NP2,P2P,P1NP);}
                GSumNat(NP2);
            }
        }
    }
}