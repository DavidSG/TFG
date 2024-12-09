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

lemma {:induction m} FSumIntComputaGSumNat(m : multiset<nat>)
ensures FSumInt(m) == GSumInt(m)

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

lemma GSumNatPartes(A:multiset<nat>, P1:multiset<nat>, P2:multiset<nat>)
    requires P1 <= A && P2 <= A && P1 + P2 == A 
    ensures GSumNat(A) == GSumNat(P1) + GSumNat(P2)
//Por induccion 

lemma GSumIntPartes(A:multiset<int>, P1:multiset<int>, P2:multiset<int>)
    requires P1 <= A && P2 <= A && P1 + P2 == A 
    ensures GSumInt(A) == GSumInt(P1) + GSumInt(P2)
//Por induccion 
