include "FSum.dfy"
include "Suma.dfy"
include "Particion.dfy"


function Suma_to_Particion(A:multiset<int>, S:int) : (r:(multiset<int>))
{
    (A + multiset{2*S - Sum(A)})
}