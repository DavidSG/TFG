include "../Auxiliar/Sum.dfy"
include "../Problems/Particion.dfy"
include "../Problems/Intervalo.dfy"


function Particion_to_Intervalo(A:multiset<int>) : (r:(multiset<int>, int, int))
{
    var S := FSum(A)/2;
    if (S % 2 == 1) then (multiset{},10,11)
    else (A, S, S+1)
    
}