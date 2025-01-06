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


lemma Particion_Envasar1(A:multiset<nat>)
    ensures var (EA,EE,Ek) := Particion_to_Envasar(A);
          Particion(A) <== Envasar(EA,EE,Ek)
{   
    // A = {1, 2, 3}
    // EA = {1, 2, 3}, EE = 3, Ek = 2
    var (EA,EE,Ek) := Particion_to_Envasar(A);
    if (Envasar(EA,EE,Ek)) {
        var C: multiset<multiset<nat>> :| forall e | e in C :: e <= EA && GSumNat(e) <= EE && |C| <= Ek && Union(C) == EA; // C = { {1,2}, {3} }
        
        assume |C| > 2;
        var P1:multiset<nat> :| P1 in C; // P1 = {1,2}
        C := C - multiset{P1}; 
        var P2:multiset<nat> :| P2 in C; // P2 = {3}

        assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);

        
     /*var C:multiset<multiset<nat>> :|
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
        */
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

        // Demostracion 1 : Union(C) == EA
        assume Union(C) == EA;

        // Demostracion 2 : forall e | e in C :: e <= EA && GSumNat(e) <= EE;
        // P1 <= EA && P2 <= EA && C = {P1,P2}
        assert P1 <= EA && P2 <= EA;

        // GSumNat(P1) <= EE && GSumNat(P2) <= EE
        FSumNatComputaGSumNat(A); // FSumInt(A)/2 && FSumInt(A) == GSumInt(A)(Funcion) => GSumInt(A)/2 == EE => GSumInt(A) = 2*EE
        GSumNatPartes(A,P1,P2); // Sum(A) = Sum (P1+P2)(Funcion) && Sum(P1) == Sum (P2) && Sum(A) = 2*EE => P1 == P2 == EE

        assert |C| <= Ek && Union(C) == EA && forall e | e in C :: e <= EA && GSumNat(e) <= EE;

        /*
        //assume P1 <= A && P2 <= A && GSumNat(P1) <= EE && GSumNat(P2) <= EE && |C| <= Ek && P1 + P2 == A;
        assume forall e | e in C :: GSumNat(e) <= EE;
        assume Union(C) == A;
        assert forall e | e in C :: e <= A && GSumNat(e) <= EE && |C| <= Ek && Union(C) == A;
        assert P1 <= A && P2 <= A 
               && GSumNat(P1) <= EE && GSumNat(P2) <= EE
               && P1 + P2 == A;
        DosMultisets(C, P1, P2);
        */
    }
}