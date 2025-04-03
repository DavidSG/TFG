include "../Auxiliar/Sum.dfy"
include "../Problems/SumaInt.dfy"
include "../Problems/SumaNat.dfy"

include "../Transformations/SumaIntToParticionInt.dfy"
include "../Transformations/ParticionIntToParticionNat.dfy"
include "../Transformations/ParticionNatToSumaNat.dfy"



function SumaInt_to_SumaNat(A:multiset<int>, S:int) : (r:(multiset<nat>,nat))
{   
    var A1 := SumaInt_to_ParticionInt(A,S); // Se añade N
    var A2 := ParticionInt_to_ParticionNat(A1); // Abs(valores negativos)
    var (A3, S3) := ParticionNat_to_SumaNat(A2);

    (A3, S3)
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

        // A El conjunto para el que queremos encontrar una solución a Suma(A,S)
        var A1 := SumaInt_to_ParticionInt(A,S); // A1 es la entrada para el problema equivalente ParticionInt(A1)
        var A2 := ParticionInt_to_ParticionNat(A1); // A2 es la entrada para el problema equivalente ParticionNat(A2)
        // SA, SS es la entrada para el problema equivalente de SumaNat(SA, SS)

        // Empleando los lemas de otros problemas justificamos que exista una solución a SumaInt(A,S)
        // Si existe una para sumaNat
        ParticionNat_Suma1(A2);
        assert ParticionNat(A2) <== SumaNat(SA,SS);

        ParticionInt_ParticionNat1(A1);
        assert ParticionInt(A1) <== ParticionNat(A2);

        SumaInt_ParticionInt1(A,S);
        assert SumaInt(A,S) <== ParticionInt(A1);
    }
}

lemma SumaInt_SumaNat2(A:multiset<int>, S:int)
    ensures var (SA, SS) := SumaInt_to_SumaNat(A, S);
          SumaInt(A,S) ==> SumaNat(SA,SS)
{

    if (SumaInt(A,S)) {
        var (SA, SS) := SumaInt_to_SumaNat(A, S);

        // A El conjunto para el que queremos encontrar una solución a Suma(A,S)
        var A1 := SumaInt_to_ParticionInt(A,S); // A1 es la entrada para el problema equivalente ParticionInt(A1)
        var A2 := ParticionInt_to_ParticionNat(A1); // A2 es la entrada para el problema equivalente ParticionNat(A2)
        // SA, SS es la entrada para el problema equivalente de SumaNat(SA, SS)

        // Empleando los lemas de otros problemas justificamos que exista una solución a SumaNat(SA,SS)
        // Si existe una para SumaInt
        SumaInt_ParticionInt2(A,S);
        assert SumaInt(A,S) ==> ParticionInt(A1);

        ParticionInt_ParticionNat2(A1);
        assert ParticionInt(A1) ==> ParticionNat(A2);

        ParticionNat_Suma2(A2);
        assert ParticionNat(A2) ==> SumaNat(SA,SS);

    }
}