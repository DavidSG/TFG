include "../Auxiliar/Sum.dfy"
include "../Problems/SumaInt.dfy"
include "../Problems/SumaNat.dfy"

function transformArray(A:multiset<int>) : (r:(multiset<nat>))
{
    if (|A| == 0) then multiset{}
    else
        var min:int := minInt(A);
        A

}

function SumaInt_to_SumaNat(A:multiset<int>, S:int) : (r:(multiset<nat>,nat))
{

    (A,S + |A|*1000)
}

lemma SumaInt_SumaNat(A:multiset<int>, S:int)
  ensures var (SA, SS):= SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) <==> SumaInt(SA, SS)
{ 
    SumaInt_SumaNat1(A,S);
    SumaInt_SumaNat2(A,S);
}

lemma SumaInt_SumaNat1(A:multiset<int>, S:int)
    ensures var (SA, SS) := SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) <== SumaNat(SA, SS)
{   
    var (SA, SS) := SumaInt_to_SumaNat(A, S);
    if (SumaNat(SA,SS)) {
        var CNat:multiset<int> :| CNat <= SA && GSumInt(CNat) == SS;

        var CInt:multiset<nat> := CInt;
        

        SumNatEqualsSumInt(CNat, CInt);
        assert CNat <= A && GSumNat(CNat) == S;
    }
}

lemma SumaInt_SumaNat2(A:multiset<int>, S:int)
    ensures var (SA, SS) := SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) ==> SumaNat(SA,SS)
{

    if (SumaInt(A,S)) {
        var (SA, SS) := SumaInt_to_SumaNat(A, S);
        var CNat:multiset<nat> :| CNat <= A && GSumNat(CNat) == S;

        var CInt:multiset<int> := CNat;
        
        SumNatEqualsSumInt(CNat, CInt);
        assert CInt <= SA && GSumInt(CInt) == SS;
    }
}