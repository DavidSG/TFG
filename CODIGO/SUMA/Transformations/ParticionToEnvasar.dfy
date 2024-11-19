include "../Auxiliar/Sum.dfy"
include "../Problems/Particion.dfy"
include "../Problems/Envasar.dfy"


function Particion_to_Envasar(A:multiset<nat>) : (r:(multiset<nat>, nat, nat))
{
    var S := FSum(A)/2;
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
    // EA = {1, 2, 3}, EE = 3, Ek = 2
    var (EA,EE,Ek) := Particion_to_Envasar(A);
    if (Envasar(EA,EE,Ek)) {
        var C: multiset<multiset<nat>> :| forall e | e in C :: e <= EA && GSum(e) <= EE && |C| <= Ek; // C = { {1,2}, {3}}
        var P1 :| P1 in C; // P1 = {1,2}
        C := C - multiset{P1}; 
        var P2 :| P2 in C; // P2 = {3}

        assert P1 in C && P2 in C && P1 != P2 && P1 * P2 == multiset{} && P1 + P2 == A && GSum(P1) == GSum(P2); // P1 y P2 son una particion de A?
    }
}


lemma Particion_Envasar2(A:multiset<nat>)
    ensures var (EA,EE,Ek) := Particion_to_Envasar(A);
          Particion(A) ==> Envasar(EA,EE,Ek)
{
    // A = {1, 2, 3}
    if (Particion(A)) {
        var (EA,EE,Ek) := Particion_to_Envasar(A);

        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 * P2 == multiset{} && P1 + P2 == A && GSum(P1) == GSum(P2); // {1,2} {3}
        var C: multiset<multiset<nat>> := multiset{P1, P2}; // { {1,2}, {3}}
        assert forall e1 | e1 in C :: (e1 <= A && GSum(e1) <= E && forall e2 | e2 in I :: e1 * e2 == multiset{}) :: |I| <= k && Union(I) == A;
    }
}