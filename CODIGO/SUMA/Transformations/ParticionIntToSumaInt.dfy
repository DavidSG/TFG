include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionInt.dfy"
include "../Problems/SumaInt.dfy"



function Particion_to_SumaInt(A:multiset<int>) : (r:(multiset<int>, int))
{
    
    if FSumInt(A) % 2 == 1 then (multiset{}, 10)
    else
    var S := FSumInt(A)/2;
    (A, S)
}

lemma Particion_Suma(A:multiset<int>)
  ensures var (SA,SS) := Particion_to_SumaInt(A);
          Particion(A) <==> SumaInt(SA,SS)
{ 
    Particion_Suma1(A);
    Particion_Suma2(A);
}

lemma Particion_Suma1(A:multiset<int>)
    ensures var (SA,SS) := Particion_to_SumaInt(A);
          Particion(A) <== SumaInt(SA,SS)
{   
    var (SA,SS) := Particion_to_SumaInt(A);
    // A = {1,2,3}
    // SA = {1,2,3} SS = 3
    if (SumaInt(SA,SS)) {
        var C:multiset<int> :| C <= SA && GSumInt(C) == SS; // {1,2}

        var P1 := C; // {1,2}
        var P2 := A - C; // {3}

        // Demostracion 1 : GSumInt(P1) == GSumInt(P2)
        FSumIntComputaGSumInt(A); // FSumInt(A)/2 && FSumInt(A) == GsumInt(A)(Funcion) => GSumInt(A)/2 == S => GSumInt(A) = 2*S 
        GSumIntPartes(A,P1,P2); // Sum(A) = Sum (P1+P2)(Funcion) && P1 == SS => P2 == SS

        assert P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);
    }
}


lemma Particion_Suma2(A:multiset<int>)
    ensures var (SA,SS) := Particion_to_SumaInt(A);
          Particion(A) ==> SumaInt(SA,SS)
{
    // A = {1, 2, 3}
    if (Particion(A)) {
        if (GSumInt(A) % 2 == 1) {
            var (SA,SS) := Particion_to_SumaInt(A);
            var S:multiset<int> := multiset{};
            assume S <= SA && GSumInt(S) == SS;
        }
        else {
            var (SA,SS) := Particion_to_SumaInt(A);
            var P1:multiset<int>, P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2); // {1,2} {3}

            var S:multiset<int> := P1;

            assume A == SA;
            
            //Demostracion 2: GSumInt(S) == SS
            FSumIntComputaGSumInt(S); FSumIntComputaGSumInt(A);
            assert GSumInt(A)/2 == SS;
            assume GSumInt(P1) == SS;

            assert S <= SA && GSumInt(S) == SS;
        }
    }
}