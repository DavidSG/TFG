include "../Auxiliar/Sum.dfy"
include "../Auxiliar/MultisetFacts.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/Envasar.dfy"

function ParticionNat_to_Envasar(A:multiset<nat>) : (r:(multiset<nat>, nat, nat))
{   

    // Si Suma(A) es impar no existe solucion a envasar con dos envases
    if (FSumNat(A) % 2 == 1) then (multiset{10}, 0, 0)
    // Se transforman los datos para el problema de envasar con dos envases
    else
    var S := FSumNat(A)/2;
    (A,S,2)
}


lemma ParticionNat_Envasar(A:multiset<nat>)
  ensures var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
          ParticionNat(A) <==> Envasar(EA,EE,Ek)
{ 
    ParticionNat_Envasar1(A);
    ParticionNat_Envasar2(A);
}


lemma  ParticionNat_Envasar1(A:multiset<nat>)
    ensures var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
          ParticionNat(A) <== Envasar(EA,EE,Ek)
{   
    var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
    if (Envasar(EA,EE,Ek)) {
        
        // Si envasar se cumple, debe exisitr un C tal que cumpla los requisitos de envasar

        // La primera es que |C| <= 1. Esto es posible si EA == {} o EA == {0}
        if (GSumNat(EA) == 0) { 
            // P1 lo igualamos a EA y P2 es el conjunto vacio. 
            var P1:multiset<nat> := EA; var P2:multiset<nat> := multiset{};

            // P1 <= A (P1 == A) y P2 <= A ({} <= A) y su suma es igual (a 0)
            assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
        }
        // La segunda es que |C| == 2. 
        else { 
            // Encontramos un C tal que sea solución a Envasar(EA,EE,EK)
            var C: multiset<multiset<nat>> :| 
            && |C| <= Ek 
            && Union(C) == EA
            && forall e | e in C :: (e <= EA && GSumNat(e) <= EE); // C = { {1,2}, {3} }

            FSumNatComputaGSumNat(A); assert GSumNat(EA) % 2 == 0;

            // Se demuestra que |C| == 2
            assert |C| == 2 by{
                // Si |C| == 0 entonces no hubiesemos entrado en este else
                if |C| == 0 {assert GSumNat(EA)/2 == 0; assert false;}

                // Si |C| == 1 demostramos que es imposible mediante reducción al absurdo.
                else if |C| == 1 {
                    Multiset1(C);

                    // Sacamos un elemento P
                    var P :| C == multiset{P};

                    // P == EA
                    calc {
                        EA;
                        Union(C); 
                        P;
                    }
                    // La Suma(P) debe ser igual a Suma(EA) (porque P es el único elemento de C)
                    assert GSumNat(P) == GSumNat(EA);

                    // La Suma(P) debe mayor que EE (Mitad de los valores de EA) 
                    // Aquí esta la contradiccion
                    assert GSumNat(P) > EE;
                    assert false;

                }
            }

            // Como sabemos que |C| == 2, se puede concluir que C == multiset{P1,P2}
            Multiset2(C); 
            var P1,P2 :| multiset{P1,P2} == C;

            // También podemos concluir que Union(C)  == P1 + P2;
            Union2(C,P1,P2);
            assert Union(C) == P1 + P2;


            assert P1 + P2 == A;

            // Empleamos este lema auxiliar para demostrar que GSumNat(P1) y GSumNat(P2) deben sumar
            // Suma(A)/2 para que se cumpla que C está formado por dos envases cuyas sumas no deben
            // superar EE (Suma(A)/2)
            GSumNatPartes(A,P1,P2);

            assert P1 <= A && P2 <= A && P1 + P2 == A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);

           
        }
    }
}



lemma ParticionImpar(A: multiset<nat>)    
    ensures  ParticionNat(A) ==> FSumNat(A) % 2 == 0
{   
    if (ParticionNat(A)){
        FSumNatComputaGSumNat(A);
    
        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
        GSumNatPartes(A,P1,P2);
        assert GSumNat(A) == GSumNat(P1) + GSumNat(P2);
        assert GSumNat(P1) + GSumNat(P2) == GSumNat(P1) + GSumNat(P1) == 2*GSumNat(P1);
        assert GSumNat(A) == 2*GSumNat(P1);
        assert GSumNat(A) % 2 == 0; 
    }
    }

lemma ParticionNat_Envasar2(A:multiset<nat>)
    ensures var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
          ParticionNat(A) ==> Envasar(EA,EE,Ek)
{
    if (ParticionNat(A)) {
        var (EA,EE,Ek) := ParticionNat_to_Envasar(A);

        ParticionImpar(A);

        assert FSumNat(A) % 2 == 0;
        assert A == EA;

        // Encontramos un P1,P2 tal que sea solución a ParticionNat(A)
        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);

        // Creamos C. C será la solución a Envasar(EA,EE,EK)
        var C: multiset<multiset<nat>> := multiset{P1,P2};

        // Demostracion Union(C) == EA      
        calc {
            Union(C);
            {Union2(C,P1,P2);}
             P1 + P2;
            EA;
        } 

        //Demostrar que P1 y P2 caben en los envases 
        assert |C|==2;
        assert P1 <= A && P2 <= A;
        FSumNatComputaGSumNat(A);
        GSumNatPartes(A,P1,P2);
    }
}
