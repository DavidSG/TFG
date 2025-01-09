include "../Auxiliar/Sum.dfy"
include "../Problems/SumaInt.dfy"
include "../Problems/ParticionInt.dfy"


function Suma_to_Particion(A:multiset<int>, S:int) : (r:(multiset<int>))
{
    var N := 2*S - FSumInt(A);
    (A + multiset{N})
}

lemma Suma_Particion(A:multiset<int>, S:int)
  ensures var PA := Suma_to_Particion(A, S);
          SumaInt(A,S) <==> Particion(PA)
{ 
    Suma_Particion1(A,S);
    Suma_Particion2(A,S);
}

lemma Suma_Particion1(A:multiset<int>, S:int)
    ensures var PA := Suma_to_Particion(A, S);
          SumaInt(A,S) <== Particion(PA)
{   
    var PA := Suma_to_Particion(A,S);
    // PA = {1, 2, 3, 4, 2(N)}   
    // S = 6
    if (Particion(PA)) {
        var N := 2*S - GSumInt(A); // N = 2
        var PA' := PA - multiset{N}; // {1, 2, 3, 4} 

        FSumIntComputaGSumInt(A); FSumIntComputaGSumInt(PA);
        GSumIntPartes(PA,A,multiset{N});
        
        var P1 :multiset<int>, P2:multiset<int> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumInt(P1) == GSumInt(P2); // P1 = {2, 4}  ->  Sum(P1) = 6

        GSumIntPartes(PA,P1,P2); // GSumInt(PA) == 2*S && GSumInt(P1) == GSumInt(P2) => GSumInt(P1) == S

        assert (P1 <= A && GSumInt(P1) == S) || (P2 <= A && GSumInt(P2) == S); // Sum(C) == 6
        
    }
}

lemma Suma_Particion2(A:multiset<int>, S:int)
    ensures var PA := Suma_to_Particion(A, S);
          SumaInt(A,S) ==> Particion(PA)
{
    // A = {1, 2, 3, 4}, S = 6
    if (SumaInt(A,S)) {
        var N := 2*S - FSumInt(A); // N = 2
        var PA := Suma_to_Particion(A,S);

        var P1:multiset<int>, P2:multiset<int> :| P1 <= A && GSumInt(P1) == S && P2 <= A && P1+P2 == A; // P1 = {2, 4}  ->  Sum(P1) = 6
           

        assume P2 <= A;

        //Demostracion 2 : GSumInt(P1) == GSumInt(P2);
        assert GSumInt(P1) == S;
        assert N == 2*S - GSumInt(A) == S - GSumInt(R);
        assert GSumInt(P2) == S;
        FSumIntComputaGSumInt(A);
        GSumIntPartes(PA,P1,P2);
        assert GSumInt(P1) == GSumInt(P2);


        assert P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumInt(P1) == GSumInt(P2); // N in PA && GSumInt(C) == GSumInt(PA') == S && C + PA' == PA; // IS <= 6 < IT
    }
}