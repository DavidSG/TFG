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
          Suma(A,S) <==> Particion(PA)
{ 
    Suma_Particion1(A,S);
    Suma_Particion2(A,S);
}

lemma Suma_Particion1(A:multiset<int>, S:int)
    ensures var PA := Suma_to_Particion(A, S);
          Suma(A,S) <== Particion(PA)
{   
    var PA := Suma_to_Particion(A,S);
    // PA = {1, 2, 3, 4, 2(N)}   
    // S = 6
    if (Particion(PA)) {
        var N := 2*S - FSumInt(A); // N = 2
        var PA' := PA - multiset{N}; // PA' = {1, 2, 3, 4} 
        
        var P1 :multiset<int> :| P1 <= PA' && GSumInt(P1) == S; // P1 = {2, 4}  ->  Sum(P1) = 6
        var P2 := PA' - P1 + multiset{N}; // P2 = {1, 3, 2} -> Sum(P2) = 6

        assert PA' <= PA && GSumInt(P1) == S; // Sum(C) == 6
    }
}

lemma Suma_Particion2(A:multiset<int>, S:int)
    ensures var PA := Suma_to_Particion(A, S);
          Suma(A,S) ==> Particion(PA)
{
    // A = {1, 2, 3, 4}, S = 6
    if (Suma(A,S)) {
        var N := 2*S - FSumInt(A); // N = 2
        var PA := Suma_to_Particion(A,S);

        var P1 : multiset<int> :| P1 <= A && GSumInt(P1) == S; // P1 = {2, 4}  ->  Sum(P1) = 6
        var R := A - P1; // R = {1, 3}
        var P2 := R + multiset{N}; // P2 = {1, 3, 2} -> Sum(P2) = 6
        
        assert GSumInt(P1) == S;
        assert GSumInt(P2) == S;

        assert A == P1 + R;
        assert GSumInt(A) == GSumInt(P1) + GSumInt(R);
        assert N == 2*S - GSumInt(A) == S - GSumInt(R);

        assert GSumInt(P1) == GSumInt(P2) == S && P1 + P2 == PA ; // N in PA && GSumInt(C) == GSumInt(PA') == S && C + PA' == PA; // IS <= 6 < IT
    }
}