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

{}

function ParticionNat_to_Intercalar (A:multiset<nat>) : (r:(seq<nat>))
{
    ([0] + multiset_to_seq(A))
}

lemma ParticionNat_Intercalar(A:multiset<nat>, S:nat)
  ensures var E := ParticionNat_to_Intercalar(A);
          ParticionNat(A) <==> Intercalar(E)
{ 
    ParticionNat_Intercalar1(A);
    ParticionNat_Intercalar2(A);
}

lemma ParticionNat_Intercalar1(A:multiset<nat>)
    ensures var E := ParticionNat_to_Intercalar(A);
          ParticionNat(A) <== Intercalar(E)
{   
    var E := ParticionNat_to_Intercalar(A);
    // E = {0, 1, 2, 3}
    if (Intercalar(E)) {
        if (|E| < 2) {
            var P1 := multiset{}; var P2 := multiset{};
            assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
        }
        else {
            // Encontramos una solucion E1,E2 a Intercalar(E)
            var elements:multiset<nat> := multiset(E);
            var E1:multiset<nat>, E2:multiset<nat> :| 
                E[0] in E1 && E1 <= elements   // E1 elementos positivos
                && E2 <= elements              // E2 elementos negativos
                && E1 + E2 == elements
                && GSumNat(E1) - GSumNat(E2) == 0;
            
            
            // Transformamos la solucion E1,E2 a P1,P2
            var P1:multiset<nat> := E1 - multiset{0};
            var P2:multiset<nat> := E2;
            
            // elements - 0 == A
            multiset_to_seqLemma(A);
            // Sum(E1) = Sum (P1+0)
            GSumNatPartes(E1,P1,multiset{0});   
            
            //Sum{0} == 0
            GSumIntElemIn(multiset{0},0);
            assert GSumInt(multiset{0}) == 0;

            // Asertamos que P1 y P2 resuelven Intercalar
            assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
        }
        
    }
}

lemma ParticionNat_Intercalar2(A:multiset<nat>)
    ensures var E := ParticionNat_to_Intercalar(A);
          ParticionNat(A) ==> Intercalar(E)
{   
    // A = {1, 2, 3},
    if (ParticionNat(A)) {
        // Encontramos la solución P1,P2 de particionNat(A)
        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); // {1,2} {3}

        // Transformamos P1,P2 en E1,E2 que resuelven Intercalar(E)
        var E := ParticionNat_to_Intercalar(A);
        var elements := multiset(E);
        
        var E1:multiset<nat> := multiset{0} + P1;
        var E2:multiset<nat> := P2;

        // elements - 0 == A
        multiset_to_seqLemma(A); 

        // Demostramos que Sum(E1) == Sum(E2)
        calc{
          GSumNat(E1);
          {GSumNatPartes(E1,P1,multiset{0});}
          GSumNat(P1) + GSumNat(multiset{0});
          // Aqui demostramos que la suma del multiset{0} == 0
          { GSumIntElemIn(multiset{0},0);
            assert GSumInt(multiset{0}) == 0;
            GSumPositiveIntNat(multiset{0});
          }
          GSumNat(P1) + 0;
          GSumNat(E2);
        }

        
        // Asertamos que E1 y E2 resuelven Intercalar
        assert  E[0] in E1 
                && E1 <= elements // E1 elementos positivos
                && E2 <= elements // E2 elementos negativos
                && E1 + E2 == elements
                && GSumNat(E1) == GSumNat(E2);

    }
}