include "../Auxiliar/Sum.dfy"
include "../Problems/SumaNat.dfy"
include "../Problems/Intervalo.dfy"


function Suma_to_Intervalo(A:multiset<nat>, S:nat) : (r:(multiset<nat>, nat, nat))
{
    (A, S, S+1)
}

lemma Suma_Intervalo(A:multiset<nat>, S:nat)
  ensures var (IE,IS,IT) := Suma_to_Intervalo(A, S);
          Suma(A,S) <==> Intervalo(IE,IS,IT)
{ 
    Suma_Intervalo1(A,S);
    Suma_Intervalo2(A,S);
}

lemma Suma_Intervalo1(A:multiset<nat>, S:nat)
    ensures var (IE,IS,IT) := Suma_to_Intervalo(A, S);
          Suma(A,S) <== Intervalo(IE,IS,IT)
{   
    var (IE,IS,IT) := Suma_to_Intervalo(A,S);
    // IE = {1, 2, 4}, IS = 6, IT = 7
    if (Intervalo(IE,IS,IT)) {
        var C:multiset<int> :| C <= A && IS <= GSumNat(C) < IT; // C = 2, 4  ->  Sum(C) = 6
        assert GSumNat(C) == S; // Sum(C) == 6
    }
}

lemma Suma_Intervalo2(A:multiset<nat>, S:nat)
    ensures var (IE,IS,IT) := Suma_to_Intervalo(A,S);
          Suma(A,S) ==> Intervalo(IE,IS,IT)
{
    // A = {1, 2, 4}, S = 6
    if (Suma(A,S)) {
        var (IE,IS,IT) := Suma_to_Intervalo(A,S);

        var C:multiset<int> :| C <= A && GSumNat(C) == S; // C = 2, 4  ->  Sum(C) = 6
        assert IS <= GSumNat(C) < IT; // IS <= 6 < IT
    }
}