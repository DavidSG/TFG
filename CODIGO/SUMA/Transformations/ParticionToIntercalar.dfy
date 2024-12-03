include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/Intercalar.dfy"

function multiset_to_seq (A:multiset<nat>) : (r:(seq<nat>)) 
{
    if A == multiset{} then [] 
  else 
  var x := minNat(A);   
   [x] + multiset_to_seq(A - multiset{x})
}

function Particion_to_Intercalar (A:multiset<nat>) : (r:(seq<nat>))
{
    ([0] + multiset_to_seq(A))
}


lemma Particion_Intercalar(A:multiset<nat>, S:nat)
  ensures var E := Particion_to_Intercalar(A);
          Particion(A) <==> Intercalar(E)
{ 
    Particion_Intercalar1(A);
    Particion_Intercalar2(A);
}

lemma Particion_Intercalar1(A:multiset<nat>)
    ensures var E := Particion_to_Intercalar(A);
          Particion(A) <== Intercalar(E)
{   
    var E := Particion_to_Intercalar(A);
    // IE = {1, 2, 4}, IS = 6, IT = 7
    if (Intercalar(E)) {
        var elements := multiset(E);
        var E1,E2 : multiset :| 
            E[0] in E1 && E1 <= elements    // E1 positive elements
            && E2 <= elements               // E2 negative elements
            && E1 + E2 == elements
            && GSumInt(E1) - GSumInt(E2) == 0;

        E1 := E1 - multiset{E[0]};

        assert E1 <= A && E2 <= A && E1 + E2 == A && GSumNat(E1) == GSumNat(E2);
    }
}

lemma Particion_Intercalar2(A:multiset<nat>)
    ensures var E := Particion_to_Intercalar(A);
          Particion(A) ==> Intercalar(E)
{
    // A = {1, 2, 4}, S = 6
    if (Particion(A)) {

        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); // {1,2} {3}

        
        var E := Particion_to_Intercalar(A);
        P1 := P1 + multiset{E[0]};
        var elements := multiset(E);
        //assert A == elements - multiset{E[0]};
        assert E[0] in P1 && P1 <= elements //E1 positive elements
            && P2 <= elements               //E2 negative elements
            && P1 + P2 == elements
            && GSumInt(P1) - GSumInt(P2) == 0;
    }
}