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

ghost function GMultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0
ensures forall e | e in r :: e > 0 && -e in A
ensures forall e | -e in A :: e in r && r[e] == A[-e]
//ensures forall e | e in A :: -e in r && r[-e] == A[e]//esto se queda colgado
ensures |A| == |r|

{
    if A == multiset{} then multiset{}
    else 
        var m :| m in A; 
        (multiset{-m} + GMultisetNegToPos(A-multiset{m}))
}

function FMultisetNegToPos(A:multiset<int>) : (r:(multiset<int>)) 
requires forall e | e in A :: e < 0
ensures r == GMultisetNegToPos(A)
{
    if A == multiset{} then multiset{}
    else 
        var min := minInt(A);
        (multiset{-min} + FMultisetNegToPos(A-multiset{min}))
}


function FMultisetAbs(A:multiset<int>) : (r:(multiset<nat>)) 
{
    FPositiveElements(A) + FMultisetNegToPos(FNegativeElements(A))
}

ghost function GPositiveElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A 
ensures forall e | e in A && e >= 0 :: e in r && r[e] == A[e]
ensures forall e | e in r :: e >= 0 
{  
    if A == multiset{} then multiset{}
    else 
        var m :| m in A;
        if m >= 0 then 
            (multiset{m} + GPositiveElements(A - multiset{m}))
        else
            (GPositiveElements(A - multiset{m}))
}

function FPositiveElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r == GPositiveElements(A)
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m >= 0 then 
            (multiset{m} + FPositiveElements(A - multiset{m}))
        else
            (FPositiveElements(A - multiset{m}))
}

ghost function GNegativeElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r <= A 
ensures forall e | e in A && e < 0 :: r[e] == A[e]
ensures forall e | e in r :: e < 0
{  
    if A == multiset{} then multiset{}
    else 
        var m :| m in A;
        if m < 0 then 
            (multiset{m} + GNegativeElements(A - multiset{m}))
        else
            (GNegativeElements(A - multiset{m}))
} 

function FNegativeElements(A:multiset<int>) : (r:(multiset<int>)) 
ensures r == GNegativeElements(A)
{  
    if A == multiset{} then multiset{}
    else 
        var m := minInt(A);
        if m < 0 then 
            (multiset{m} + FNegativeElements(A - multiset{m}))
        else
            (FNegativeElements(A - multiset{m}))
}


lemma dafnyEsTonto(A:multiset<int>, x:int, i:int)
requires x >= FSumNat(FMultisetAbs(A))
ensures i + x >= 0

function FMultisetAdd(A:multiset<int>, x:int) : (r:(multiset<nat>)) 
requires x >= FSumNat(FMultisetAbs(A))
ensures forall e | e in A :: A[e] == r[e+x]
/*{  
    if A == multiset{} then multiset{}
    else 
        var i := minInt(A);
        assert i + x >= 0;
        (multiset{i+x} + FMultisetAdd(A - multiset{i},x))
}*/

function repeat(value:nat, amount:nat) : (r:(multiset<nat>)) 
ensures r[value] == amount
{  
    if amount == 0 then multiset{}
    else 
        (multiset{value} + repeat(value,amount-1))
}

lemma SumAbsGtSum(A: multiset<int>)
ensures FSumNat(FMultisetAbs(A)) >= FSumInt(A)


function SumaInt_to_SumaNat(A:multiset<int>, S:int) : (r:(multiset<nat>,nat))
{   
    SumAbsGtSum(A);
    var absSum := FSumNat(FMultisetAbs(A));
    var SA:multiset<nat> := FMultisetAdd(A,absSum) + repeat(absSum, |A|);
    var SS:int := S + |A|*absSum;

    if (SS < 0) then (multiset{}, 5)
    else (SA,SS)
}


lemma SumaInt_SumaNat(A:multiset<int>, S:int)
    ensures var (SA, SS):= SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) <==> SumaNat(SA, SS)
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
        var CNat:multiset<nat> :| CNat <= SA && GSumNat(CNat) == SS;

        var CInt:multiset<int> := MultisetNatToInt(CNat);

        assume CInt <= A && GSumInt(CInt) == S;
    }
}

lemma SumaInt_SumaNat2(A:multiset<int>, S:int)
    ensures var (SA, SS) := SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) ==> SumaNat(SA,SS)
{

    if (SumaInt(A,S)) {
        var (SA, SS) := SumaInt_to_SumaNat(A, S);
        var CInt:multiset<int> :| CInt <= A && GSumInt(CInt) == S;

        var CNat:multiset<nat> := MultisetIntToNat(CInt);
        
        assume CNat <= SA && GSumNat(CNat) == SS;
    }
}