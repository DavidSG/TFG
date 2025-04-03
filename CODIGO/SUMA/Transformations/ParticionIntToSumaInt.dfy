include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionInt.dfy"
include "../Problems/SumaInt.dfy"

function ParticionInt_to_SumaInt(A:multiset<int>) : (r:(multiset<int>, int))
{
    
    if (FSumInt(A) % 2 == 1) then (multiset{}, 10)
    else
    var S := FSumInt(A)/2; (A, S)
}

lemma NotSumaInt()
ensures !SumaInt(multiset{},10)
{  assert GSumInt(multiset{}) == 0 != 10;}

lemma ParticionInt_Suma(A:multiset<int>)
  ensures var (SA,SS) := ParticionInt_to_SumaInt(A);
          ParticionInt(A) <==> SumaInt(SA,SS)
{ 
    ParticionInt_Suma1(A);
    ParticionInt_Suma2(A);
}

lemma ParticionInt_Suma1(A:multiset<int>)
    ensures var (SA,SS) := ParticionInt_to_SumaInt(A);
          ParticionInt(A) <== SumaInt(SA,SS)
{   
    var (SA,SS) := ParticionInt_to_SumaInt(A);
    
    // Demostramos por reduccion al absurdo que si SumaNat(SA,SS) tiene solución 
    // significa que la suma de los elementos es par, porque si no la transformación 
    // hubiese devuelto (multiset{}, 10), que es un problema sin solución
    if (SumaInt(SA,SS)) {
        assert FSumInt(A) % 2 != 1 by{
           if( FSumInt(A) % 2 == 1)
            {assert (SA,SS) == (multiset{},10);
             NotSumaInt();
             assert false;}
        }
        FSumIntComputaGSumInt(A); 

        // Encontramos una solución C al problema SumaNat(SA,SS) 
        var C:multiset<int> :| C <= SA && GSumInt(C) == SS; // {1,2}

        // Como la suma de los elementos de C es igual a suma(A)/2, 
        // si igualamos P1 a C, será una particion tal que su suma es suma(A)/2
        var P1 := C; 
        var P2 := A - C; // P2 es el resto de elementos de A

        // Si P1 == SS y P2 == SS Suma(P1) == Suma(P2)
        GSumIntPartes(A,P1,P2); 

        // P1 y P2 resuelven ParticionNat(A) son subconjuntos de PA (que es igual a A) y su suma es igual
        assert P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);
    }
}


lemma ParticionInt_Suma2(A:multiset<int>)
    ensures var (SA,SS) := ParticionInt_to_SumaInt(A);
          ParticionInt(A) ==> SumaInt(SA,SS)
{
    // A = {1, 2, 3}
    var (SA,SS) := ParticionInt_to_SumaInt(A);
    if (ParticionInt(A)) {
        // Encontramos una solución P1,P2 al problema ParticionNat(A)
        var P1:multiset<int>, P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2); 

        // Si Suma(P1) == Suma(P2) entonces Suma(P1) == Suma(P2) == Suma(A)/2
        GSumIntPartes(A,P1,P2);

        // Suma(A) tiene que ser un número par. Por tanto, en la transformación SA == A
        assert GSumInt(A) == 2 * GSumInt(P1);
        FSumIntComputaGSumInt(A);
        assert FSumInt(A) % 2 == 0;
        
        // Sabemos que P1 <= A, y que A == SA. También sabemos que Suma(P1) == Suma(A)/2,
        // y que Suma(A)/2 == SS. Por tanto P1 es una solución a Suma(SA,SS)
        var S:multiset<int> := P1;
        assert S <= SA && GSumInt(S) == SS;
    }
}