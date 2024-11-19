include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Particion.dfy"


function Particion_to_Envasar(A:multiset<int>) : (r:(multiset<int>, int, int))
{
    var S := FSum(A)/2;
    (A, S,2)
}