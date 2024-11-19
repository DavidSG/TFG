include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Particion.dfy"


function Suma_to_Particion(A:multiset<int>, S:int) : (r:(multiset<int>))
{
    var N := 2*S - FSumInt(A);
    (A + multiset{N})
}

lemma Suma_Particion(A:multiset<int>, S:int)
  ensures var (PA) := Suma_to_Particion(A, S);
          Suma(A,S) <==> Particion(PA)
{ 
    Suma_Particion1(A,S);
    Suma_Particion2(A,S);
}

lemma Suma_Particion1(A:multiset<int>, S:int)
    ensures var (PA) := Suma_to_Particion(A, S);
          Suma(A,S) <== Particion(PA)
{   
    var (PA) := Suma_To_Intervalo(A,S);
    // PA = {1, 2, 3, 4, 2(N)}
    if (Particion(PA)) {
        var C:multiset<int> :| C <= A && IS <= GSum(C) < IT; // C = 2, 4  ->  Sum(C) = 6
        assert GSum(C) == S; // Sum(C) == 6
    }
}

lemma Suma_Particion2(A:multiset<int>, S:int)
    ensures var (PA) := Suma_to_Particion(A, S);
          Suma(A,S) ==> Particion(PA)
{
    // A = {1, 2, 4}, S = 6
    if (Suma(A,S)) {
        var (PA) := Suma_To_Intervalo(A,S);

        var C:multiset<int> :| C <= A && GSum(C) == S; // C = 2, 4  ->  Sum(C) = 6
        assert IS <= GSum(C) < IT; // IS <= 6 < IT
    }
}