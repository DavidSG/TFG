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
    if (SumaInt(SA,SS)) {
        var C:multiset<int> :| C <= SA && GSumInt(C) == SS;

        var CNat:multiset<nat> := C;
        assert forall e | e in C :: e >= 0;
        
        assert CNat <= A && GSumNat(CNat) == S;
    }
}

lemma SumaNat_SumaInt2(A:multiset<nat>, S:nat)
    ensures var (SA, SS) := SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) ==> SumaInt(SA,SS)
{

    if (SumaNat(A,S)) {
        var (SA, SS) := SumaNat_to_SumaInt(A, S);
        var C:multiset<nat> :| C <= A && GSumNat(C) == S;

        var CInt:multiset<int> := C;
        
        assert CInt <= SA && GSumInt(CInt) == SS;
    }
}