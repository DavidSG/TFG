include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Particion.dfy"


function Particion_To_Suma(A:multiset<int>) : (r:(multiset<int>, int))
{
    var S := FSum(A)/2;
    if (S % 2 == 1) then (multiset{},10)
    else (A, S)
}