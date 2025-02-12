include "../Auxiliar/Sum.dfy"
include "../Problems/SumaInt.dfy"
include "../Problems/ParticionInt.dfy"


function SumaInt_to_ParticionInt(A:multiset<int>, S:int) : (r:(multiset<int>))
{
    var N := 2*S - FSumInt(A);
    (A + multiset{N})
}

lemma SumaInt_ParticionInt(A:multiset<int>, S:int)
  ensures var PA := SumaInt_to_ParticionInt(A, S);
          SumaInt(A,S) <==> ParticionInt(PA)
{ 
    SumaInt_ParticionInt1(A,S);
    SumaInt_ParticionInt2(A,S);
}

lemma SumaInt_ParticionInt1(A:multiset<int>, S:int)
    ensures var PA := SumaInt_to_ParticionInt(A, S);
          SumaInt(A,S) <== ParticionInt(PA)
{   
    var PA := SumaInt_to_ParticionInt(A,S);
    // PA = {1, 2, 3, 4, 2(N)}   
    // S = 6
    //reveal GSumInt();
    if (ParticionInt(PA)) {
        FSumIntComputaGSumInt(A); 
        var N := 2*S - GSumInt(A); // N = 2
        GSumIntPartes(PA,A,multiset{N});
        
        var P1 :multiset<int>, P2:multiset<int> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumInt(P1) == GSumInt(P2); // P1 = {2, 4}  ->  Sum(P1) = 6

        GSumIntPartes(PA,P1,P2); // GSumInt(PA) == 2*S && GSumInt(P1) == GSumInt(P2) => GSumInt(P1) == S
        //assert GSumInt(P1) == GSumInt(P2) == S;
        assert (P1 <= A && GSumInt(P1) == S) || (P2 <= A && GSumInt(P2) == S); // Sum(C) == 6
    }
}

lemma SumaInt_ParticionInt2(A:multiset<int>, S:int)
    ensures var PA := SumaInt_to_ParticionInt(A, S);
          SumaInt(A,S) ==> ParticionInt(PA)
{
    // A = {1, 2, 3, 4}, S = 6
    if (SumaInt(A,S)) {
        //reveal GSumInt();
        FSumIntComputaGSumInt(A);
        var PA := SumaInt_to_ParticionInt(A, S);
        var N := 2*S - GSumInt(A); // N = 2
        GSumIntPartes(PA,A,multiset{N}); // PA == A + N;

        var C :| C <= A && GSumInt(C) == S;
        var P1:multiset<int> := C; var P2:multiset<int> := A-C+multiset{N};

        GSumIntPartes(PA,P1,P2);

        assert P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumInt(P1) == GSumInt(P2); // N in PA && GSumInt(C) == GSumInt(PA') == S && C + PA' == PA; // IS <= 6 < IT
        existsPartition(PA,P1,P2);

    }
}