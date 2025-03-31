include "../Auxiliar/Sum.dfy"
include "../Problems/ParticionInt.dfy"
include "../Problems/SumaInt.dfy"

function ParticionInt_to_SumaInt(A:multiset<int>) : (r:(multiset<int>, int))
{
    
    if (FSumInt(A) % 2 == 1) then (multiset{}, 10)
    else
    var S := FSumInt(A)/2; (A, S)
}

lemma NotSumaInt()
ensures !SumaInt(multiset{},10)
{  //reveal GSumInt();
    assert GSumInt(multiset{}) == 0 != 10;}

lemma ParticionInt_Suma(A:multiset<int>)
  ensures var (SA,SS) := ParticionInt_to_SumaInt(A);
          ParticionInt(A) <==> SumaInt(SA,SS)
{ 
    ParticionInt_Suma1(A);
    ParticionInt_Suma2(A);
}

lemma ParticionInt_Suma1(A:multiset<int>)
    ensures var (SA,SS) := ParticionInt_to_SumaInt(A);
          ParticionInt(A) <== SumaInt(SA,SS)
{   
    var (SA,SS) := ParticionInt_to_SumaInt(A);
    // A = {1,2,3}
    // SA = {1,2,3} SS = 3
    
    if (SumaInt(SA,SS)) {
        assert FSumInt(A) % 2 != 1 by{
            //reveal GSumInt();
           if( FSumInt(A) % 2 == 1)
            {assert (SA,SS) == (multiset{},10);
             NotSumaInt();
             assert false;}
        }
        FSumIntComputaGSumInt(A); 

        var C:multiset<int> :| C <= SA && GSumInt(C) == SS; // {1,2}

        var P1 := C; // {1,2}
        var P2 := A - C; // {3}

        // Demostracion: GSumInt(P1) == GSumInt(P2)
        GSumIntPartes(A,P1,P2); // Sum(A) = Sum (P1+P2)(Funcion) && P1 == SS => P2 == SS
        assert P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2);
        existsPartition(A,P1,P2);
    }
}


lemma ParticionInt_Suma2(A:multiset<int>)
    ensures var (SA,SS) := ParticionInt_to_SumaInt(A);
          ParticionInt(A) ==> SumaInt(SA,SS)
{
    // A = {1, 2, 3}
    var (SA,SS) := ParticionInt_to_SumaInt(A);
    if (ParticionInt(A)) {
            var P1:multiset<int>, P2:multiset<int> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumInt(P1) == GSumInt(P2); // {1,2} {3}
            GSumIntPartes(A,P1,P2);
            assert GSumInt(A) == 2 * GSumInt(P1);
            FSumIntComputaGSumInt(A);
            assert FSumInt(A) % 2 == 0;
             
            var S:multiset<int> := P1;
            assert S <= SA && GSumInt(S) == SS;
    }
}