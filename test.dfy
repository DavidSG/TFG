lemma test ()
ensures !exists x : int :: 2 * x == 5
{
        if (exists x : int :: 2 * x == 5) {
                assert false;
        }   
}


lemma EcuacionSinSentido ()
ensures !exists x : int :: x + 3 == x
{
        if (exists x : int ::  x + 3 == x) {
                assert 3 == 0;
                assert false;
        }   
}

lemma PropiedadSuma (n : nat)
requires n >= 1
ensures n < n + 1
{
        if (n == 1) {
                assert 1 < 2;
        }
        else {
                PropiedadSuma(n - 1);
                assert n - 1 < n ;
                assert n - 1 + 1 < n + 1;
                assert n < n + 1;
        }
}
