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

lemma multiset_to_seqLemma (A:multiset<nat>)
    ensures A == multiset(multiset_to_seq(A))

{
    var SA := multiset(multiset_to_seq(A));
    assert A == SA;
}

function Particion_to_Intercalar (A:multiset<nat>) : (r:(seq<nat>))
{
    ([0] + multiset_to_seq(A))
}


lemma SumaMulticonjuntos(M1:multiset<nat>, M2:multiset<nat>)
    ensures GSumNat(M1) + GSumNat(M2) == GSumNat(M1+M2)

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
    // E = {0, 1, 2, 3}
    if (Intercalar(E)) {
        if (|E| < 2) {
            var P1 := multiset{}; var P2 := multiset{};
            assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
        }
        else {
            var elements:multiset<nat> := multiset(E);
            var E1:multiset<nat>, E2:multiset<nat> :| 
                E[0] in E1 && E1 <= elements    // E1 positive elements
                && E2 <= elements               // E2 negative elements
                && E1 + E2 == elements
                && GSumNat(E1) - GSumNat(E2) == 0;
            
            
            var P1:multiset<nat> := E1 - multiset{0};
            var P2:multiset<nat> := E2;
            
            // Demostracion 1: elements - 0 == A
            multiset_to_seqLemma(A); // E == [0] + multiset_to_seq(A) && multiset(multiset_to_seq(A)) == A =>
                                     // => multiset{E} - multiset{0} == A

            // Demostracion 2: Sum(P1) = Sum (E1-0)
            assert E1 == P1 + multiset{0}; SumaMulticonjuntos(P1,multiset{0});
            assert GSumNat(E1) == GSumNat(P1) + GSumNat(multiset{0});
            
            assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
        }
        
    }
}

lemma Particion_Intercalar2(A:multiset<nat>)
    ensures var E := Particion_to_Intercalar(A);
          Particion(A) ==> Intercalar(E)
{
    // A = {1, 2, 3},
    if (Particion(A)) {
        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); // {1,2} {3}

        var E := Particion_to_Intercalar(A);
        var elements := multiset(E);

        var E1:multiset<nat> := multiset{0} + P1;
        var E2:multiset<nat> := P2;

        // Demostracion 1: 0 + A = elements
        multiset_to_seqLemma(A); // multiset([0] + multiset_to_seq(A)) == elements

        // Demostracion 2: Sum(E1) = Sum (0+P1)
        assert E1 == P1 + multiset{0}; SumaMulticonjuntos(P1,multiset{0});
        assert GSumNat(E1) == GSumNat(P1) + GSumNat(multiset{0});
          
        assert  E[0] in E1 
                && E1 <= elements //E1 elementos positivos
                && E2 <= elements //E2 elementos negativos
                && E1 + E2 == elements
                && GSumNat(E1) == GSumNat(E2);
    }
}