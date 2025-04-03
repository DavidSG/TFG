include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/SumaNat.dfy"

function ParticionNat_to_SumaNat(A:multiset<nat>) : (r:(multiset<nat>, nat))
{
    // Si la Suma(A) es impar, Particion(A) no tiene solución
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
        // Demostramos por reduccion al absurdo que si SumaNat(SA,SS) tiene solución 
        // significa que la suma de los elementos es par, porque si no la transformación 
        // hubiese devuelto (multiset{}, 10), que es un problema sin solución
        assert FSumNat(A) % 2 != 1 by{
            assume FSumNat(A) % 2 == 1;
            assert (SA,SS) == (multiset{},10);
            NotSumaNat();
            assert false;
        }
        FSumNatComputaGSumNat(A); 

        // Encontramos una solución C al problema SumaNat(SA,SS) 
        var C:multiset<nat> :| C <= SA && GSumNat(C) == SS; 

        // Como la suma de los elementos de C es igual a suma(A)/2, 
        // si igualamos P1 a C, será una particion tal que su suma es suma(A)/2
        var P1 := C; 
        var P2 := A - C; // P2 es el resto de elementos de A

        // Si P1 == SS y P2 == SS Suma(P1) == Suma(P2)
        GSumNatPartes(A,P1,P2); 

        // P1 y P2 resuelven ParticionNat(A) son subconjuntos de PA (que es igual a A) y su suma es igual
        assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
    }
}


lemma ParticionNat_Suma2(A:multiset<nat>)
    ensures var (SA,SS) := ParticionNat_to_SumaNat(A);
          ParticionNat(A) ==> SumaNat(SA,SS)
{
    var (SA,SS) := ParticionNat_to_SumaNat(A);
    if (ParticionNat(A)) {
        // Encontramos una solución P1,P2 al problema ParticionNat(A)
        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); 

        // Si Suma(P1) == Suma(P2) entonces Suma(P1) == Suma(P2) == Suma(A)/2
        GSumNatPartes(A,P1,P2);

        
        assert GSumNat(A) == 2 * GSumNat(P1);
        FSumNatComputaGSumNat(A);
        assert FSumNat(A) % 2 == 0;
        
        // Sabemos que P1 <= A, y que A == SA. También sabemos que Suma(P1) == Suma(A)/2,
        // y que Suma(A)/2 == SS. Por tanto P1 es una solución a Suma(SA,SS)
        var S:multiset<nat> := P1;
        assert S <= SA && GSumNat(S) == SS;
    }
}