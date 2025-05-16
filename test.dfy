lemma test ()
ensures !exists x1 : real :: x1 > 0.0 && forall y : real :: (x1 < y)
{
        assume exists x1 : real :: x1 > 0.0 && (forall y : real :: x1 < y);
        var x1 : real :| x1 > 0.0 && (forall y : real :: x1 < y);
        //assert exists x2 : real | x2 == x1 / 2.0 :: x2 > 0.0 && x1 < x2;
        assume false;    
}