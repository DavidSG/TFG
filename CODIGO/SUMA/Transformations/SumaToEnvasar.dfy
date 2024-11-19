include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Envasar.dfy"


function Suma_to_Envasar(A:multiset<int>, S:int) : (r:(multiset<int>, int, int))
{
    var N := 2*S - FSum(A);
    (A + multiset{N}, S,2)
}