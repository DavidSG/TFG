include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Intervalo.dfy"


function Suma_To_Intervalo(A:multiset<int>, S:int) : (r:(multiset<int>, int, int))
{
    (A, S, S+1)
}

lemma Suma_Intervalo(A:multiset<int>, S:int)
  ensures var (IE,IS,IT) := Suma_To_Intervalo(A, S);
          Suma(A,S) <==> Intervalo(IE,IS,IT)
{ 
    Suma_Intervalo1(A,S);
    Suma_Intervalo2(A,S);
}

lemma Suma_Intervalo1(A:multiset<int>, S:int)
    ensures var (IE,IS,IT) := Suma_To_Intervalo(A, S);
          Suma(A,S) <== Intervalo(IE,IS,IT)
{   
    var (IE,IS,IT) := Suma_To_Intervalo(A,S);
    // IE = {1, 2, 4}, IS = 6, IT = 7
    if (Intervalo(IE,IS,IT)) {
        var C:multiset<int> :| C <= A && IS <= GSum(C) < IT; // C = 2, 4  ->  Sum(C) = 6
        assert GSum(C) == S; // Sum(C) == 6
    }
}

lemma Suma_Intervalo2(A:multiset<int>, S:int)
    ensures var (IE,IS,IT) := Suma_To_Intervalo(A,S);
          Suma(A,S) ==> Intervalo(IE,IS,IT)
{
    // A = {1, 2, 4}, S = 6
    if (Suma(A,S)) {
        var (IE,IS,IT) := Suma_To_Intervalo(A,S);

        var C:multiset<int> :| C <= A && GSum(C) == S; // C = 2, 4  ->  Sum(C) = 6
        assert IS <= GSum(C) < IT; // IS <= 6 < IT
    }
}

