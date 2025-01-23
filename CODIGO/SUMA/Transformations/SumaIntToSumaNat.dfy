include "../Auxiliar/Sum.dfy"
include "../Problems/SumaInt.dfy"
include "../Problems/SumaNat.dfy"

function MultisetIntToNat(A:multiset<int>) : (r:(multiset<nat>))
    requires forall e | e in A :: e > -10 && e < 10
{
    if (|A| == 0) then multiset{}
    else
        var min:int := minInt(A);
        var minNat := (min + 1000) as nat;
        multiset{minNat} + MultisetIntToNat(A-multiset{min})

}

function MultisetNatToInt(A:multiset<nat>) : (r:(multiset<int>))
{
    if (|A| == 0) then multiset{}
    else
        var min:nat := minNat(A);
        var minInt := min - 1000;
        if (minInt == 0) then MultisetNatToInt(A-multiset{min}) else multiset{minInt} + MultisetNatToInt(A-multiset{min})
}

lemma aux (A:multiset<int>)
    requires forall e | e in A :: e > -10 && e < 10
    ensures MultisetNatToInt(MultisetIntToNat(A)) == A

function SumaInt_to_SumaNat(A:multiset<int>, S:int) : (r:(multiset<nat>,nat))
    requires forall e | e in A :: e > -10 && e < 10
    requires S > -10 && S < 10
{
    var SA:multiset<nat> := MultisetIntToNat(A);
    var SS:nat := S+|A|*1000;
    (SA,SS)
}

lemma SumaInt_SumaNat(A:multiset<int>, S:int)
    requires forall e | e in A :: e > -10 && e < 10
    requires S > -10 && S < 10
    ensures var (SA, SS):= SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) <==> SumaNat(SA, SS)
{ 
    SumaInt_SumaNat1(A,S);
    SumaInt_SumaNat2(A,S);
}

lemma SumaInt_SumaNat1(A:multiset<int>, S:int)
requires forall e | e in A :: e > -10 && e < 10
    requires S > -10 && S < 10
    ensures var (SA, SS) := SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) <== SumaNat(SA, SS)
{   
    var (SA, SS) := SumaInt_to_SumaNat(A, S);
    if (SumaNat(SA,SS)) {
        var CNat:multiset<nat> :| CNat <= SA && GSumNat(CNat) == SS;

        var CInt:multiset<int> := MultisetNatToInt(CNat);

        assume CInt <= A && GSumInt(CInt) == S;
    }
}

lemma SumaInt_SumaNat2(A:multiset<int>, S:int)
requires forall e | e in A :: e > -10 && e < 10
    requires S > -10 && S < 10
    ensures var (SA, SS) := SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) ==> SumaNat(SA,SS)
{

    if (SumaInt(A,S)) {
        var (SA, SS) := SumaInt_to_SumaNat(A, S);
        var CInt:multiset<int> :| CInt <= A && GSumInt(CInt) == S;

        var CNat:multiset<nat> := MultisetIntToNat(CInt);
        
        assert MultisetIntToNat(A) == SA;
        assume CNat <= SA && GSumNat(CNat) == SS;
    }
}