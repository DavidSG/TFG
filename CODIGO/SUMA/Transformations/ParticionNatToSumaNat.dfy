include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/SumaNat.dfy"

function ParticionNat_to_SumaNat(A:multiset<nat>) : (r:(multiset<nat>, nat))
{
    
    if (FSumNat(A) % 2 == 1) then (multiset{}, 10)
    else
    var S := FSumNat(A)/2; (A, S)
}

lemma NotSumaNat()
ensures !SumaNat(multiset{},10)
{  
     assert GSumNat(multiset{}) == 0 != 10;
}

lemma ParticionNat_Suma(A:multiset<nat>)
  ensures var (SA,SS) := ParticionNat_to_SumaNat(A);
          ParticionNat(A) <==> SumaNat(SA,SS)
{ 
    ParticionNat_Suma1(A);
    ParticionNat_Suma2(A);
}

lemma ParticionNat_Suma1(A:multiset<nat>)
    ensures var (SA,SS) := ParticionNat_to_SumaNat(A);
          ParticionNat(A) <== SumaNat(SA,SS)
{   
    var (SA,SS) := ParticionNat_to_SumaNat(A);
    
    if (SumaNat(SA,SS)) {
        assert FSumNat(A) % 2 != 1 by{
            assume FSumNat(A) % 2 == 1;
            assert (SA,SS) == (multiset{},10);
            NotSumaNat();
            assert false;
        }
        FSumNatComputaGSumNat(A); 

        var C:multiset<nat> :| C <= SA && GSumNat(C) == SS; // {1,2}

        var P1 := C; // {1,2}
        var P2 := A - C; // {3}

        // Demostracion: GSumNat(P1) == GSumNat(P2)
        GSumNatPartes(A,P1,P2); // Sum(A) = Sum (P1+P2)(Funcion) && P1 == SS => P2 == SS
        assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
    }
}


lemma ParticionNat_Suma2(A:multiset<nat>)
    ensures var (SA,SS) := ParticionNat_to_SumaNat(A);
          ParticionNat(A) ==> SumaNat(SA,SS)
{
    // A = {1, 2, 3}
    var (SA,SS) := ParticionNat_to_SumaNat(A);
    if (ParticionNat(A)) {
            var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); 
            GSumNatPartes(A,P1,P2);
            assert GSumNat(A) == 2 * GSumNat(P1);
            FSumNatComputaGSumNat(A);
            assert FSumNat(A) % 2 == 0;
             
            var S:multiset<nat> := P1;
            assert S <= SA && GSumNat(S) == SS;
    }
}