include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Particion.dfy"


function Suma_to_Particion(A:multiset<int>, S:int) : (r:(multiset<int>))
{
    (A + multiset{2*S - FSum(A)})
}