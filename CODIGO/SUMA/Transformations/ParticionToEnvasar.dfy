include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Particion.dfy"


function Particion_to_Envasar(A:multiset<int>) : (r:(multiset<int>, int, int))
{
    (A, FSum(A)/2,2)
}