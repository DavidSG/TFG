include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Particion.dfy"


function Particion_To_Suma(A:multiset<int>) : (r:(multiset<int>, int))
{
    (A, FSum(A)/2)
}