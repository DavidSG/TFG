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

function minNat(m:multiset<nat>): (l:nat)
ensures l in m && (forall x | x in m :: x <= l) 

function minInt(m:multiset<int>): (l:int)
ensures l in m && (forall x | x in m :: x <= l) 


lemma {:induction m} FSumNatComputaGSumNat(m : multiset<nat>)
ensures FSumNat(m) == GSumNat(m)


function FSumNat(m : multiset<nat>) : nat
{
  if m == multiset{} then 0 
  else 
  var x := minNat(m); 
  x + FSumNat(m - multiset{x})
}

function FSumInt(m : multiset<int>) : int
{
  if m == multiset{} then 0 
  else 
  var x := minInt(m);   
  x + FSumInt(m - multiset{x})
}
ghost function GSumInt(m: multiset<int>) : int
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumInt(m - multiset{x})
}

ghost function GSumNat(m: multiset<nat>) : nat
{
  if m == multiset{} then 0
  else var x :| x in m; x + GSumNat(m - multiset{x})
}
