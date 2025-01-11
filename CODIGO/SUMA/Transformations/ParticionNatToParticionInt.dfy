include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/ParticionInt.dfy"

function multisetNatToInt(A : multiset<nat>) : (r:(multiset<int>))
    requires forall e | e in A :: e >= 0
    ensures A == r;

{
    if A == multiset{} then multiset{}
    else var i := minInt(A) as int; multiset{i} + multisetNatToInt(A-multiset{i})
}

lemma SumNatEqualsSumInt (A:multiset<nat>, B: multiset<int>)
    requires forall e | e in B :: e >= 0
    requires A == B
    ensures GSumNat(A) == GSumInt(B)
{   
    if (A == multiset{}) {
        assert B == multiset{};
        assert GSumNat(A) == GSumInt(B);
    }
    else {
        var ai := minNat(A);
        var bi := minInt(B);
        SumNatEqualsSumInt(A-multiset{ai}, B-multiset{bi});
        assert ai == bi && GSumNat(A-multiset{ai}) == GSumInt(B-multiset{bi}); 
        GSumNatPartes(A,multiset{ai},A-multiset{ai}); GSumIntPartes(B,multiset{bi},B-multiset{bi});
        assert GSumNat(A) == GSumInt(B);
         
    }
}

    

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

        var test1:multiset<nat> := multiset{1,2}; var test2:multiset<int> := multiset{1,2};

        assume GSumNat(NP1) == GSumNat(NP2);
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

        SumNatEqualsSumInt(NP1,IP1); SumNatEqualsSumInt(NP2,IP2);
        assert IP1 <= PA && IP2 <= PA && IP1 + IP2 == PA && GSumInt(IP1) == GSumInt(IP2);
    }
}