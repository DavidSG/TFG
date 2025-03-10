include "../Auxiliar/Sum.dfy"
include "../Auxiliar/MultisetFacts.dfy"
include "../Problems/ParticionNat.dfy"
include "../Problems/Envasar.dfy"

function ParticionNat_to_Envasar(A:multiset<nat>) : (r:(multiset<nat>, nat, nat))
{
    if (FSumNat(A) % 2 == 1) then (multiset{10}, 0, 0)
    else
    var S := FSumNat(A)/2;
    (A,S,2)
}


lemma ParticionNat_Envasar(A:multiset<nat>)
  ensures var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
          ParticionNat(A) <==> Envasar(EA,EE,Ek)
{ 
    ParticionNat_Envasar1(A);
    ParticionNat_Envasar2(A);
}


lemma UnionOne(C: multiset<multiset<nat>>, P1:multiset<nat>)
requires P1 in C
ensures Union(C) == P1 + Union(C-multiset{P1})
/*{ var i:| i in C && Union(C) == i + Union(C-multiset{i});
 if (i == P1){   
 }
 else {
    assert P1 in C-multiset{i};
    UnionOne(C-multiset{i},P1);
    
    }
 
}*/

lemma Union2(C: multiset<multiset<nat>>,P1: multiset<nat>, P2: multiset<nat>)
requires C == multiset{P1,P2}
ensures Union(C) == P1 + P2
{
 UnionOne(C,P1);
 assert Union(C) == P1 + Union(C-multiset{P1});
 UnionOne(C-multiset{P1},P2);
 assert Union(C-multiset{P1}) == Union((C-multiset{P1})-multiset{P2})+ P2;
 assert (C-multiset{P1})-multiset{P2} == multiset{};
 assert  Union(C)  == P1 + P2;
}


lemma Multiset2(C: multiset<multiset<nat>>)
requires |C| == 2
ensures exists P1,P2 :: multiset{P1,P2} == C
{
    var P1:multiset<nat> :| P1 in C; 
    // assert P1 < EA; // P1 = {1,2}
    var CC := C - multiset{P1};
    SubstractUnion(multiset{P1},C);
    assert  CC + multiset{P1} == C ;
    
    assert |CC| > 0;
    var P2:multiset<nat> :| P2 in CC; 
    var CC' := CC - multiset{P2};
    SubstractUnion(multiset{P2},CC);
    assert  CC' + multiset{P2} == CC ;
    assert CC' == multiset{};
    assert CC' + multiset{P2} == multiset{P2};
    assert (CC' + multiset{P2}) + multiset{P1} == multiset{P1,P2};
    assert (CC' + multiset{P2}) + multiset{P1} == C;
    assert multiset{P1,P2} == C;


}


lemma ParticionNat_Envasar1(A:multiset<nat>)
    ensures var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
          ParticionNat(A) <== Envasar(EA,EE,Ek)
{   
    // A = {1, 2, 3}
    // EA = {1, 2, 3}, EE = 3, Ek = 2
    var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
    if (Envasar(EA,EE,Ek)) {
     
        // Demostrar: |C| == 2;
        if (GSumNat(EA) == 0) { // |C| < 2
            var P1:multiset<nat> := EA; var P2:multiset<nat> := multiset{};
            assert P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);
        }
        else { //|C| == 2;
            var C: multiset<multiset<nat>> :| 
            && |C| <= Ek 
            && Union(C) == EA
            && forall e | e in C :: (e <= EA && GSumNat(e) <= EE); // C = { {1,2}, {3} }

            FSumNatComputaGSumNat(A); assert GSumNat(EA) % 2 == 0;

            //Demostrar que multiset{P1,P2} == C
            assert |C| == 2 by{
              if |C| == 0 {assert GSumNat(EA)/2 == 0; assert false;}
              else if |C| == 1 {
                var e:| e in C && C-multiset{e} == multiset{};
                assume false;

              }
            


            }
             Multiset2(C); 
             var P1,P2 :| multiset{P1,P2} == C;

            //Demostrar que Union(C) == P1 + P2
            Union2(C,P1,P2);
            assert Union(C)  == P1 + P2;
            //Demostrar que: P1 + P2 == A
            //assert C - multiset{P1} - multiset{P2} == multiset{};
            //assert P1 in C && P2 in C && Union(C) == A && P1 <= A && P2 <= A;
            assert P1 + P2 == A;

            //Demostracion 4: GSumNat(P1) == GSumNat(P2)
            //assert GSumNat(A) == GSumNat(P1) + GSumNat(P2) && GSumNat(EA) == 2*EE && GSumNat(P1) <= EE && GSumNat(P2) <= EE;
            GSumNatPartes(A,P1,P2);

            assert P1 <= A && P2 <= A && P1 + P2 == A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2);

           
        }
        

        
     /*var C:multiset<multiset<nat>> :|
        && |C| <= Ek 
        && Union(C) == EA
        && forall e | e in C :: e <= EA && GSumNat(e) <= EE ;

        var P1:| P1 in C; // P1 = {1,2}
        assert GSumNat(P1) <= EE;
        var PP := C - multiset{P1};
        assume PP != multiset{}; //Reduccion al absurdo |C|<=2
        var P2:| P2 in PP; // P2 = {3}
        assume P1 + P2 == EA; // P1 + P2 = {1,2} + {3} = {1,2,3}
        GSumNatPartes(EA, P1, P2);
        FSumNatComputaGSumNat(EA);
        */
    }
}
lemma N2IsEven(A: int) 
    ensures (2*A) % 2 == 0
{}

lemma Equality(A: multiset<nat>, P1: multiset<nat>, P2: multiset<nat>)
    requires P1 <= A && P2 <= A && P1 + P2 == A
    ensures GSumNat(P1) == GSumNat(P2) <==> GSumNat(P1) == GSumNat(A)/2 && GSumNat(P2) == GSumNat(A)/2
{

}

lemma ParticionImpar(A: multiset<nat>) 
    ensures ParticionNat(A) ==> FSumNat(A) % 2 == 0
{   
    assume FSumNat(A) % 2 == 1;
    FSumNatComputaGSumNat(A);
    assert !exists P1:multiset<nat>, P2:multiset<nat> | P1 <= A && P2 <= A && P1 + P2 == A :: GSumNat(P1) == GSumNat(P2) by {
        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A;
        assume GSumNat(P1) == GSumNat(P2);
        Equality(A,P1,P2); // P1 y P2 tienen que sumar la mitad de A para ser iguales
        GSumNatPartes(A,P1,P2);
        
        var half := GSumNat(A)/2;
        N2IsEven(half); // Si hay dos mitades que suman lo mismo, A tiene que ser par

        assert GSumNat(A) % 2 == 0; // CONTRADICCION, A tiene que ser par

        assert false;
    }
    
    assume false;
}

lemma ParticionNat_Envasar2(A:multiset<nat>)
    ensures var (EA,EE,Ek) := ParticionNat_to_Envasar(A);
          ParticionNat(A) ==> Envasar(EA,EE,Ek)
{
    // A = {1, 2, 3}
    if (ParticionNat(A)) {
        var (EA,EE,Ek) := ParticionNat_to_Envasar(A);

        //assert
        ParticionImpar(A);

        assert FSumNat(A) % 2 == 0;
        assert A == EA;

        var aux:multiset<nat> := multiset{1,2,3};
        var x:multiset<nat> :| x <= aux;

        var P1:multiset<nat>, P2:multiset<nat> :| P1 <= A && P2 <= A && P1 + P2 == A && GSumNat(P1) == GSumNat(P2); // {1,2} {3}
        var C: multiset<multiset<nat>> := multiset{P1,P2}; // { {1,2}, {3}}

        // Demostracion Union(C) == EA
        //PRE: assert C == multiset{P1,P2};
        Union2(C,P1,P2);
        //POST: assert Union(C) == P1 + P2;
        assert P1 + P2 == EA;
        assume Union(C) == EA;
                
        assert P1 <= EA && P2 <= EA;

        // GSumNat(P1) <= EE && GSumNat(P2) <= EE
        FSumNatComputaGSumNat(A); // FSumInt(A)/2 && FSumInt(A) == GSumInt(A)(Funcion) => GSumInt(A)/2 == EE => GSumInt(A) = 2*EE
        GSumNatPartes(A,P1,P2); // Sum(A) = Sum (P1+P2)(Funcion) && Sum(P1) == Sum (P2) && Sum(A) = 2*EE => P1 == P2 == EE

        assert |C| <= Ek && Union(C) == EA && forall e | e in C :: e <= EA && GSumNat(e) <= EE;
    }
}