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

function FSum(m : multiset<int>) : int
{
  if m == multiset{} then 0 
  else 
  var x :| x in m; 
  x + FSum(m - multiset{x})
}

ghost function GSum(m : multiset<int>) : int
{
	if m == multiset{} then 0 
  else var x :| x in m; x + GSum(m - multiset{x})
}
