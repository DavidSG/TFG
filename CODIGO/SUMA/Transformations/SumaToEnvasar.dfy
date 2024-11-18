include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Envasar.dfy"


function Particion_to_Envasar(A:multiset<int>, S:int) : (r:(multiset<int>, int, int))
{
    (A + multiset{2*S - FSum(A)}, FSum(A)/2,2)
}