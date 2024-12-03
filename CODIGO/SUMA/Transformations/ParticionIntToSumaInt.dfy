include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionInt.dfy"
include "../Problems/SumaInt.dfy"



function Particion_to_Suma(A:multiset<int>) : (r:(multiset<int>, int))
{
    
    if FSumInt(A) % 2 == 1 then (multiset{}, 10)
    else
    var S := FSumInt(A)/2;
    (A, S)
}

lemma Particion_Suma(A:multiset<int>)
  ensures var (SA,SS) := Particion_to_Suma(A);
          Particion(A) <==> Suma(SA,SS)
{ 
    Particion_Suma1(A);
    Particion_Suma2(A);
}

lemma Particion_Suma1(A:multiset<int>)
    ensures var (SA,SS) := Particion_to_Suma(A);
          Particion(A) <== Suma(SA,SS)
{   
    var (SA,SS) := Particion_to_Suma(A);
    // A = {1,2,3}
    // SA = {1,2,3} SS = 3
    if (Suma(SA,SS)) {
        var C:multiset<int> :| C <= SA && GSumInt(C) == SS; // {1,2}

        var P1 := C; // {1,2}
        var P2 := A - C; // {3}

        assert P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);
    }
}

lemma Particion_Suma2(A:multiset<int>)
    ensures var (SA,SS) := Particion_to_Suma(A);
          Particion(A) ==> Suma(SA,SS)
{
    // A = {1, 2, 3}
    if (Particion(A)) {
        var (SA,SS) := Particion_to_Suma(A);
        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); // {1,2} {3}     

        assert P1 <= SA && GSumInt(P1) == SS;
    }
}