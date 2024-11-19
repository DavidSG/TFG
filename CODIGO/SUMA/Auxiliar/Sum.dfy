// funcion auxiliar
/*
function FSum(m : multiset<int>) : int
{
  var mCopy := m; 
  var total := 0;
  
	while ( mCopy != multiset{} )
    decreases mCopy;
  {
    var x :| x in mCopy;
    mCopy := mCopy - { x };
  }

  total
}
*/

function FSum(m : multiset<T>) : nat
{
  if m == multiset{} then 0 
  else 
  var x :| x in m; 
  x + FSum(m - multiset{x})
}

type Num =  int | nat;
ghost function GSum<T: Num>(m: multiset<T>) : T
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSum(m - multiset{x})
}
