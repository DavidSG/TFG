include "../Auxiliar/Sum.dfy"
include "../Problems/SumaInt.dfy"
include "../Problems/ParticionInt.dfy"


function SumaInt_to_ParticionInt(A:multiset<int>, S:int) : (r:(multiset<int>))
{
    var N := 2*S - FSumInt(A);
    (A + multiset{N})
}

lemma SumaInt_ParticionInt(A:multiset<int>, S:int)
  ensures var PA := SumaInt_to_ParticionInt(A, S);
          SumaInt(A,S) <==> ParticionInt(PA)
{ 
    SumaInt_ParticionInt1(A,S);
    SumaInt_ParticionInt2(A,S);
}

lemma SumaInt_ParticionInt1(A:multiset<int>, S:int)
    ensures var PA := SumaInt_to_ParticionInt(A, S);
          SumaInt(A,S) <== ParticionInt(PA)
{   
    var PA := SumaInt_to_ParticionInt(A,S);

    if (ParticionInt(PA)) {
        FSumIntComputaGSumInt(A); 
        var N := 2*S - GSumInt(A); 
        GSumIntPartes(PA,A,multiset{N});

        // Encontramos dos multisets P1,P2 tal que cumplen ParticionInt(A,S)
        var P1 :multiset<int>, P2:multiset<int> :| P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumInt(P1) == GSumInt(P2); 

        // Sabemos que PA == P1 + P2, por lo que podemos emplear GSumIntPartes(PA,P1,P2)
        // Un lemma que asegura que suma(PA) == Suma (P1) + Suma(P2)
        GSumIntPartes(PA,P1,P2); 

        // P1 cumple SumaInt(A,S) o P2 cumple SumaInt(A,S) ya que el otro tendrá N
        assert (P1 <= A && GSumInt(P1) == S) || (P2 <= A && GSumInt(P2) == S); // Sum(C) == 6
    }
}

lemma SumaInt_ParticionInt2(A:multiset<int>, S:int)
    ensures var PA := SumaInt_to_ParticionInt(A, S);
          SumaInt(A,S) ==> ParticionInt(PA)
{
    if (SumaInt(A,S)) {
    
        FSumIntComputaGSumInt(A);
        var PA := SumaInt_to_ParticionInt(A, S);
        var N := 2*S - GSumInt(A); // N = 2
        GSumIntPartes(PA,A,multiset{N}); // PA == A + N;

        // Encontramos una solución C a Suma(A,S)
        var C :| C <= A && GSumInt(C) == S;

        // Encontramos la solución a Partición a partir de C
        var P1:multiset<int> := C; var P2:multiset<int> := A-C+multiset{N};

        GSumIntPartes(PA,P1,P2);

        assert P1 <= PA && P2 <= PA && P1 + P2 == PA && GSumInt(P1) == GSumInt(P2); 

    }
}