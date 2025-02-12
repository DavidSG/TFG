include "../Auxiliar/Sum.dfy"
include "../Problems/SumaNat.dfy"
include "../Problems/SumaInt.dfy"

function SumaNat_to_SumaInt(A:multiset<nat>, S:nat) : (r:(multiset<int>,int))
{
    (A,S)
}

lemma SumaNat_SumaInt(A:multiset<nat>, S:nat)
  ensures var (SA, SS):= SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) <==> SumaInt(SA, SS)
{ 
    SumaNat_SumaInt1(A,S);
    SumaNat_SumaInt2(A,S);
}

lemma SumaNat_SumaInt1(A:multiset<nat>, S:nat)
    ensures var (SA, SS) := SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) <== SumaInt(SA, SS)
{   
    var (SA, SS) := SumaNat_to_SumaInt(A, S);
    if (SumaInt(SA,SS)) {
        var CInt:multiset<int> :| CInt <= SA && GSumInt(CInt) == SS;

        var CNat:multiset<nat> := CInt;
        

        GSumPositiveIntNat(CNat);
        assert CNat <= A && GSumNat(CNat) == S;
    }
}

lemma SumaNat_SumaInt2(A:multiset<nat>, S:nat)
    ensures var (SA, SS) := SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) ==> SumaInt(SA,SS)
{

    if (SumaNat(A,S)) {
        var (SA, SS) := SumaNat_to_SumaInt(A, S);
        var CNat:multiset<nat> :| CNat <= A && GSumNat(CNat) == S;

        var CInt:multiset<int> := CNat;
        
        GSumPositiveIntNat(CNat);
        assert CInt <= SA && GSumInt(CInt) == SS;
    }
}