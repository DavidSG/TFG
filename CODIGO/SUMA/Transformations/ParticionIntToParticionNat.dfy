include "../Auxiliar/Sum.dfy"
include "../Auxiliar/MultisetFacts.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

ghost function GMultisetPosToNeg(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e > 0
ensures forall e | e in r :: e < 0 && -e in A
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

// Nuevo
lemma {:induction P} GPositiveUnionOneElement(P: multiset<int>, p: int)
requires p >= 0
ensures GPositiveElements(P + multiset{p}) == GPositiveElements(P) + multiset{p}
{}

/*lemma {:induction P} GNegativeUnionOneElement(P: multiset<int>, p: int)
requires p >= 0
ensures GNegativeElements(P + multiset{p}) == GNegativeElements(P) + multiset{p}
*/

lemma GPositiveUnion(P1: multiset<int>, P2: multiset<int>)
    ensures GPositiveElements(P1 + P2) == GPositiveElements(P1) + GPositiveElements(P2)
{}
/*if (P1 == multiset{}){}
 else 
 {
   var p1:| p1 in P1; 
   if (p1 < 0) {}
   else {
     
     ghost var P1S := P1 - multiset{p1};   
     assert P1S < P1;
     GPositiveUnion(P1S,P2);
     assert GPositiveElements(P1S + P2) == GPositiveElements(P1S) + GPositiveElements(P2);
     assert P1 + P2 == (P1S + P2) + multiset{p1} by{
        calc{
            P1 + P2;
            (P1S + multiset{p1}) + P2;
            {AssociativeUnion(P1S,multiset{p1},P2);
            CommutativeUnion(multiset{p1},P2);
            }
            P1S + (P2 + multiset{p1});
            {AssociativeUnion(P1S,P2,multiset{p1});}
            (P1S + P2) + multiset{p1};

                } 
            }
            GPositiveUnionOneElement(P1S+P2,p1);
            assert GPositiveElements(P1S + P2 + multiset{p1}) ==  GPositiveElements(P1S + P2) + multiset{p1};
        } 

    }*/


lemma GNegativeUnion(P1: multiset<int>, P2: multiset<int>)
    ensures GNegativeElements(P1 + P2) == GNegativeElements(P1) + GNegativeElements(P2)
{}

lemma GMultisetNegToPosUnion(P1: multiset<int>, P2: multiset<int>)
     requires forall e | e in P1 :: e < 0
     requires forall e | e in P2 :: e < 0
     ensures GMultisetNegToPos(P1 + P2) == GMultisetNegToPos(P1) + GMultisetNegToPos(P2)
{}

lemma GMultisetNegToPosSingle(i:int)
     requires i < 0
     ensures GMultisetNegToPos(multiset{i}) == multiset{-i}
{}

lemma GMultisetPosToNegSingle(i:int)
     requires i > 0
     ensures GMultisetPosToNeg(multiset{i}) == multiset{-i}
{}

lemma GMultisetPosToNegToPosSingle(i:int)
     requires i > 0
     ensures GMultisetNegToPos(GMultisetPosToNeg(multiset{i})) == multiset{i}
{}


lemma GMultisetNegToPosToNegSingle(i:int)
     requires i < 0
     ensures GMultisetPosToNeg(GMultisetNegToPos(multiset{i})) == multiset{i}
{}

lemma GSumNatMultisetNegToPosSingle(i:int)
     requires i < 0
     ensures GSumNat(GMultisetNegToPos(multiset{i})) == -i
{
  GMultisetNegToPosSingle(i);
  assert GSumNat(GMultisetNegToPos(multiset{i}))== GSumNat(multiset{-i});
  GSumIntElem(multiset{},-i);
  assert GSumInt(multiset{-i}) == -i;
  GSumPositiveIntNat(multiset{-i});
}

lemma GMultisetPosToNegUnion(P1: multiset<int>, P2: multiset<int>)
     requires forall e | e in P1 :: e > 0
     requires forall e | e in P2 :: e > 0
     ensures GMultisetPosToNeg(P1 + P2) == GMultisetPosToNeg(P1) + GMultisetPosToNeg(P2)
{}

lemma GMultisetNegToPosToNeg(A: multiset<int>)
requires forall e | e in A :: e < 0
ensures GMultisetPosToNeg(GMultisetNegToPos(A)) == A
{
 if (A == multiset{}) {}
 else {

    var i:| i in A;
    var AI := A - multiset{i};
    assert A == AI + multiset{i};
    if AI == multiset{} { 
        assert A == multiset{i};
       GMultisetNegToPosToNegSingle(i);
     }
    else {
        var GA := GMultisetNegToPos(A);
        var GAI := GMultisetNegToPos(AI);
        var GI := GMultisetNegToPos(multiset{i});
        assert GA == GAI + GI by{
          GMultisetNegToPosUnion(AI,multiset{i});

        }
        calc{
          A;
          AI + multiset{i};
          {GMultisetNegToPosToNeg(AI);}
          GMultisetPosToNeg(GMultisetNegToPos(AI)) + multiset{i} ;
          {GMultisetNegToPosToNegSingle(i);
           assert multiset{i} == GMultisetPosToNeg(GMultisetNegToPos(multiset{i}));
          }
          GMultisetPosToNeg(GMultisetNegToPos(AI)) +  GMultisetPosToNeg(GMultisetNegToPos(multiset{i}));
          GMultisetPosToNeg(GAI) + GMultisetPosToNeg(GI);
          {GMultisetPosToNegUnion(GAI,GI);}
          GMultisetPosToNeg(GAI +  GI);
          GMultisetPosToNeg(GA);
        } 
  }
 }

}

lemma GMultisetPosToNegToPos(A: multiset<int>)
requires forall e | e in A :: e > 0
ensures GMultisetNegToPos(GMultisetPosToNeg(A)) == A
{

if (A == multiset{}) {}
 else {

    var i:| i in A;
    var AI := A - multiset{i};
    assert A == AI + multiset{i};
    if AI == multiset{} { 
        assert A == multiset{i};
       GMultisetPosToNegToPosSingle(i);
     }
    else {
        var GA := GMultisetPosToNeg(A);
        var GAI := GMultisetPosToNeg(AI);
        var GI := GMultisetPosToNeg(multiset{i});
        assert GA == GAI + GI by{
          GMultisetPosToNegUnion(AI,multiset{i});

        }
        calc{
          A;
          AI + multiset{i};
          {GMultisetPosToNegToPos(AI);}
          GMultisetNegToPos(GMultisetPosToNeg(AI)) + multiset{i} ;
          {GMultisetPosToNegToPosSingle(i);
           assert multiset{i} == GMultisetNegToPos(GMultisetPosToNeg(multiset{i}));
          }
          GMultisetNegToPos(GMultisetPosToNeg(AI)) +  GMultisetNegToPos(GMultisetPosToNeg(multiset{i}));
          GMultisetNegToPos(GAI) + GMultisetNegToPos(GI);
          {GMultisetNegToPosUnion(GAI,GI);}
          GMultisetNegToPos(GAI +  GI);
          GMultisetNegToPos(GA);
        } 
  }
 }

}

lemma NegSumGMultisetNegToPos(A:multiset<int>)
requires forall e | e in A :: e < 0
ensures GSumNat(GMultisetNegToPos(A)) == - GSumInt(A)
{
    if (A == multiset{}) {

    }
    else {
        var i :| i in A;
        var I := multiset{i};
        var AI := A - multiset{i};
        assert A == AI + I;
        calc {
            - GSumInt(A);
            {GSumIntPartes(A,AI,I);}
            - GSumInt(AI) - i;
            {NegSumGMultisetNegToPos(AI);}
            GSumNat(GMultisetNegToPos(AI)) - i;
            { GSumNatMultisetNegToPosSingle(i);}
             GSumNat(GMultisetNegToPos(AI)) + GSumNat(GMultisetNegToPos(I));
            {   GMultisetNegToPosUnion(AI,I);
                GSumNatPartes(GMultisetNegToPos(A),GMultisetNegToPos(AI),GMultisetNegToPos(I));}
            GSumNat(GMultisetNegToPos(A));
        }
    }
}

lemma SumGPositiveNegativeElements(A:multiset<int>)
ensures GSumNat(GPositiveElements(A)) == GSumInt(GPositiveElements(A))
ensures GSumNat(GMultisetNegToPos(GNegativeElements(A))) == -GSumInt(GNegativeElements(A))
{GSumPositiveIntNat(GPositiveElements(A));
 NegSumGMultisetNegToPos(GNegativeElements(A));
}

lemma  Partes(A:multiset<int>)
    ensures A == GPositiveElements(A) + GNegativeElements(A) 
    ensures GPositiveElements(A) * GNegativeElements(A) == multiset{}
{ }

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
     Partes(A);
    var PA := ParticionInt_to_ParticionNat(A);
    if (ParticionNat(PA)) {
        var P1:multiset<nat>,P2:multiset<nat> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumNat(P1) == GSumNat(P2);

        Partes(A);
        ghost var AP:multiset<int> := GPositiveElements(A);
        ghost var AN:multiset<int> := GNegativeElements(A);
        ghost var ANP:multiset<int>:= GMultisetNegToPos(AN);
        assert A == AP + AN;
        //assert PA == AP + ANP; 
        assert ANP == PA - AP; 
        
        ghost var P1P:multiset<int> := P1 * AP;
        IntersectionContained(P1,AP);
        assert P1P <= AP;

        ghost var P2P:multiset<int> := AP - P1P;
        ghost var P1NP:multiset<int> := P1 - P1P;
        ghost var P2NP:multiset<int> := P2 - P2P;
        ghost var P1N:multiset<int> := GMultisetPosToNeg(P1NP);
        ghost var P2N:multiset<int> := GMultisetPosToNeg(P2NP);
        ghost var IP1:multiset<int> := P1P + P2N; 
        ghost var IP2:multiset<int> := P2P + P1N;

        assert P1P + P2P == AP by{
            assert P2P == (AP - P1P);
            assert P1P + P2P == P1P + (AP - P1P);
            SubstractUnion(P1P, AP);
        }
        assert P1 == P1P + P1NP && P2 == P2P + P2NP by{
            SubstractUnion(P1P,P1);
            SubstractUnion(P2P,P2);       
        }

        assert GMultisetNegToPos(AN) == P1NP + P2NP by {
            calc{
                    GMultisetNegToPos(AN);//by definition 
                    ANP;
                    PA - AP;
                    {
                        assert PA == P1 + P2;
                        assert AP == P1P + P2P;
                    }
                    (P1 + P2) - (P1P + P2P);
                    {UnionSubstractUnion(P1,P2,P1P,P2P);}
                    (P1 - P1P) + (P2 - P2P);
                    P1NP + P2NP; 
            }
        }

        assert AN == P1N + P2N by {
            calc{ 
            AN;
            {GMultisetNegToPosToNeg(AN);}
            GMultisetPosToNeg(GMultisetNegToPos(AN));
            GMultisetPosToNeg(P1NP + P2NP);
            {GMultisetPosToNegUnion(P1NP,P2NP);}
            GMultisetPosToNeg(P1NP) + GMultisetPosToNeg(P2NP);
            P1N + P2N;
            }
        }

        assert A == IP1 + IP2 by{
            calc{
            A;
            AP + AN;
            (P1P + P2P) + (P1N + P2N);
            {CommutativeAssociativeUnion(P1P,P2P,P1N,P2N);}
            (P1P + P2N) + (P2P + P1N);
            IP1 + IP2;
            }
        }
       
        assert IP1 <= A && IP2 <= A;

        assert GSumInt(P1P) == GSumNat(P1P) &&
               GSumInt(P2P) == GSumNat(P2P) 
        by{
            GSumPositiveIntNat(P1P);
            GSumPositiveIntNat(P2P);
        }
        
        assert GSumNat(P2NP) == -GSumInt(P2N) &&
               GSumNat(P1NP) == -GSumInt(P1N)
        
         by{
          assert P1NP == GMultisetNegToPos(GMultisetPosToNeg(P1NP))
          by{GMultisetPosToNegToPos(P1NP);}
          
          assert P2NP == GMultisetNegToPos(GMultisetPosToNeg(P2NP))
          by{GMultisetPosToNegToPos(P2NP);}
       
          calc{
            -GSumInt(P2N);
            {assert P2N == GMultisetPosToNeg(P2NP);}
            -GSumInt(GMultisetPosToNeg(P2NP));
            {NegSumGMultisetNegToPos(GMultisetPosToNeg(P2NP));
            }
            GSumNat(P2NP);
          } 
          calc{
            -GSumInt(P1N);
            {assert P1N == GMultisetPosToNeg(P1NP);}
            -GSumInt(GMultisetPosToNeg(P1NP));
            {NegSumGMultisetNegToPos(GMultisetPosToNeg(P1NP));
            }
            GSumNat(P1NP);
          } 
        }

        
        assert GSumNat(P1P) - GSumNat(P2NP) == GSumNat(P2P) - GSumNat(P1NP) by
        {                            
            GSumNatPartes(P1,P1P,P1NP);
            GSumNatPartes(P2,P2P,P2NP);
        }

        assert GSumInt(IP1) == GSumInt(IP2) by{
            calc{
            GSumInt(IP1);
            {assert IP1 == P1P + P2N;}
            GSumInt(P1P + P2N);
            {GSumIntPartes(IP1,P1P,P2N);}
            GSumInt(P1P) + GSumInt(P2N);
            GSumNat(P1P) - GSumNat(P2NP);
            GSumNat(P2P) - GSumNat(P1NP); 
            GSumInt(P2P) + GSumInt(P1N);  
            {GSumIntPartes(IP2,P2P,P1N);}
            {assert IP2 == P2P + P1N;}
            GSumInt(IP2);
          }
        }

        assert IsPartitionInt(A,IP1,IP2);
        existsPartition(A,IP1,IP2);
        assert ParticionInt(A);
    }
}


lemma ParticionInt_ParticionNat2(A:multiset<int>)
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