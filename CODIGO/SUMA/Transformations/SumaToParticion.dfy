include "../Auxiliar/Sum.dfy"
include "../Problems/Suma.dfy"
include "../Problems/Particion.dfy"


function Suma_to_Particion(A:multiset<int>, S:int) : (r:(multiset<int>))
{
    var N := 2*S - FSum(A);
    (A + multiset{N})
}