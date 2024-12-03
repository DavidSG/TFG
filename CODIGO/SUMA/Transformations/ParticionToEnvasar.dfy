include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/Envasar.dfy"

function Particion_to_Envasar(A:multiset<nat>) : (r:(multiset<nat>, nat, nat))
{
    var S := FSumNat(A)/2;
    (A,S,2)
}

lemma Particion_Envasar(A:multiset<nat>)
  ensures var (EA,EE,Ek) := Particion_to_Envasar(A);
          Particion(A) <==> Envasar(EA,EE,Ek)
{ 
    Particion_Envasar1(A);
    Particion_Envasar2(A);
}

lemma GSumNatPartes(A:multiset<nat>, P1:multiset<nat>, P2:multiset<nat>)
    requires P1 <= A && P2 <= A && P1 + P2 == A 
    ensures GSumNat(A) == GSumNat(P1) + GSumNat(P2)
//Por induccion 

lemma Particion_Envasar1(A:multiset<nat>)
    ensures var (EA,EE,Ek) := Particion_to_Envasar(A);
          Particion(A) <== Envasar(EA,EE,Ek)
{   
    // A = {1, 2, 3}
    // EA = {1, 2, 3}, EE = 3, Ek = 2
    var (EA,EE,Ek) := Particion_to_Envasar(A);
    if (Envasar(EA,EE,Ek)) {
    var C:multiset<multiset<nat>> :|
        && |C| <= Ek 
        && Union(C) == EA
        && forall e | e in C :: e <= EA && GSumNat(e) <= EE ;

        var P1:| P1 in C; // P1 = {1,2}
        assert GSumNat(P1) <= EE;
        var PP := C - multiset{P1};
        assume PP != multiset{}; //Reduccion al absurdo |C|<=2
        var P2:| P2 in PP; // P2 = {3}
        assume P1 + P2 == EA; // P1 + P2 = {1,2} + {3} = {1,2,3}
        GSumNatPartes(EA, P1, P2);
        FSumNatComputaGSumNat(EA);
    }
}

lemma {:axiom} DosMultisets(A:multiset<multiset<nat>>, P1:multiset<nat>, P2:multiset<nat>)
    requires A == multiset{P1,P2}
    ensures Union(A) == P1 + P2

lemma  Particion_Envasar2(A:multiset<nat>)
    ensures var (EA,EE,Ek) := Particion_to_Envasar(A);
          Particion(A) ==> Envasar(EA,EE,Ek)
{
    // A = {1, 2, 3}
    if (Particion(A)) {
        var (EA,EE,Ek) := Particion_to_Envasar(A);

        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); // {1,2} {3}
        var C: multiset<multiset<nat>> := multiset{P1, P2}; // { {1,2}, {3}}
        FSumNatComputaGSumNat(EA);
        GSumNatPartes(EA, P1, P2);

        assert P1 <= A && P2 <= A 
               && GSumNat(P1) <= EE && GSumNat(P2) <= EE
               && P1 + P2 == A;
        DosMultisets(C, P1, P2);
    }
}