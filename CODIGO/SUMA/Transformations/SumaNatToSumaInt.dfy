include "../Auxiliar/Sum.dfy"
include "../Problems/SumaNat.dfy"
include "../Problems/SumaInt.dfy"


function SumaNat_to_SumaInt(A:multiset<nat>, S:nat) : (r:(multiset<int>,int))
{
    (A,S)
}

lemma SumaNat_SumaInt(A:multiset<nat>, S:nat)
  ensures var (SA, SS):= SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) <==> SumaNat(SA, SS)
{ 
    SumaNat_SumaInt1(A,S);
    SumaNat_SumaInt2(A,S);
}

lemma SumaNat_SumaInt1(A:multiset<nat>, S:nat)
    ensures var (SA, SS) := SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) <== SumaInt(SA, SS)
{   
    var (SA, SS) := SumaNat_to_SumaInt(A, S);
    if (SumaInt(A,S)) {
        var C:multiset<int> :| C <= A && GSumInt(C) == S;
        
        assert C <= SA && GSumNat(C) == SS;
    }
}

lemma SumaNat_SumaInt2(A:multiset<nat>, S:nat)
    ensures var (SA, SS) := SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) ==> SumaInt(SA,SS)
{

    if (SumaNat(A,S)) {
        var C:multiset<nat> :| C <= A && GSumNat(C) == S;
        
        assert C <= AA && GSumInt(C) == S;
    }
}