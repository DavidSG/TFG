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
        // Se selecciona un subconjunto CInt que resuelva SumaInt(SA, SS)
        var CInt:multiset<int> :| CInt <= SA && GSumInt(CInt) == SS;

        // Como todos los elementos de SA son positivos (los elementos de A son positivos y A == SA)
        // Podemos transformar CInt a CNat
        var CNat:multiset<nat> := CInt;
        
        // GSumInt(CInt) == GSumNat(CNat)
        GSumPositiveIntNat(CNat);

        // CNat resuelve SumaNat(A,S)
        assert CNat <= A && GSumNat(CNat) == S;
    }
}

lemma SumaNat_SumaInt2(A:multiset<nat>, S:nat)
    ensures var (SA, SS) := SumaNat_to_SumaInt(A, S);
          SumaNat(A,S) ==> SumaInt(SA,SS)
{

    if (SumaNat(A,S)) {
        var (SA, SS) := SumaNat_to_SumaInt(A, S);

        // Se selecciona un subconjunto CNat que resuelva SumaNat(A,S)
        var CNat:multiset<nat> :| CNat <= A && GSumNat(CNat) == S;

        // Transformamos CNat a CInt
        // Todos los naturales son enteros
        var CInt:multiset<int> := CNat;
        
        // GSumInt(CInt) == GSumNat(CNat)
        GSumPositiveIntNat(CNat);

        // CInt resuelve SumaNat(A,S)
        assert CInt <= SA && GSumInt(CInt) == SS;
    }
}