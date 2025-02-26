lemma CommutativeUnion<T>(x:multiset<T>,y:multiset<T>)
ensures x + y == y + x
{
    // We form multisets A and B from the equations in the ensures clause
    var A := x + y;
    var B := y + x;

    // The multiplicities of elements in A and of elements in B are the same via induction, implemented here as the equal operator (==)
    assert A == B;
}

lemma AssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures x + (y + z) == (x + y) + z
{
    // We form multisets A and B from the equations in the ensures clause
    var A := x + (y + z);
    var B := (x + y) + z;

    // The multiplicities of elements in A and of elements in B are the same via induction, implemented here as the equal operator (==)
    assert A == B;
}

lemma CommutativeAssociativeUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
ensures (x + y) + (z + u) == (x + u) + (y + z)
{
    // We form multisets A and B from the equations in the ensures clause
    var A := (x + y) + (z + u);
    var B := (x + u) + (y + z);

    // The multiplicities of elements in A and of elements in B are the same via induction, implemented here as the equal operator (==)
    assert A == B;
} 

lemma IntersectionContained<T>(A: multiset<T>,B:multiset<T>)
ensures A * B <= A && A * B <= B
{


}

lemma IntersectionUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
requires  z >=  x + y
ensures (x + y) * z == (x * z + y * z)
{ 
    
}

lemma IntersectionUnionContained<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>)
ensures  x * z + y * z >= (x + y) * z
{   

}

lemma SubstractUnion<T>(x:multiset<T>,y:multiset<T>)
requires y >= x
ensures x + (y - x) == y
{} 

lemma UnionSubstractUnion<T>(x:multiset<T>,y:multiset<T>,z:multiset<T>,u:multiset<T>)
requires x + y >= z + u && x >= z && y >= u
ensures (x + y) - (z + u) == (x - z) + (y - u)
{}