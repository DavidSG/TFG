// funcion auxiliar

ghost function Sum(m : multiset<int>) : int
{
	if m == multiset{} then 0 
  else var x :| x in m; x + Sum(m - multiset{x})
}
