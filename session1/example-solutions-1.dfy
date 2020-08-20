
//  Find a loop invariant and prove termination.

/**
 *  Example 0.a.
 *  Counter-example generation.
 */
method abs (x: int) returns (y : int)
    ensures  0 <= y; 
{
    if (x < 0) {
        return -x;
    } else {
        return x;
    }
}

/**
 *  Example 0.b.
 *  
 *  Try to:
 *  1. write the post-condition that shows that max larger than x and y.
 *  2. write a set of post-conditions that fully characterises max.
 *  3. make sure it verifies.
 */
method max (x: int, y: int) returns (m : int)
    requires true
    ensures m == y || m == x
    ensures m >= x && m >= y
{
    var r : int;
    if ( x < y ) {
        r := y  ;
    } else {
        r := x;
    }
    m := r;
    //  can use return r instead
    return m;
}

/**
 *  Example 1.
 *  
 *  Try to prove 
 *  1. the final assert statement.
 *  2. termination.
 */
method ex1 (n: int) returns (i : int)
    requires n >= 0
    ensures i == n
    // decreases *
{
    i := 0;
    while (i < n)
        invariant i <= n;
        decreases n - i;   
    {
        i := i + 1;
        assert( i <= n);
    } // i <= n && !(i < n) <==> i == n
    /** This is the property to prove: */
    assert i == n;
}

//  Specify a post-condition and prove it.

/**
 *  Example 2.
 *
 *  Find a key in an array.
 *
 *  @param      a   The array.
 *  @param      key The key to find.
 *  @returns        An index i such a[i] == key if key in a and -1 otherwise.
 *
 *  Try to:
 *  1. write the property defined by the returns
 *  2. prove this property (add loop invariants)
 */
method find (a: seq<int>, key: int) returns (index : int)
    requires true
    ensures key !in a ==> index == -1 
    ensures key in a ==> 0 <= index < |a| 
    ensures key in a ==> 0 <= index < |a| && a[index] == key
{
    index := 0;
    while (index < |a|) 
        decreases |a| - index
        invariant 0 <= index <= |a| ;
        invariant key !in a[..index];
        {
            if ( a[index] == key ) { 
                assert( index < |a|);
                return index ;
            }
            index := index + 1;
        }
    index := -1;
}

/**
 *  Whether a sequence of ints is sorted (ascending).
 */
predicate sorted (a: seq<int>) 
{
    forall j, k::0 <= j < k < |a|  ==> a[j] <= a[k]
}

//  Prove more complicated invariants with quantifiers.

/**
 *  Example 3.
 *
 *  Remove duplicates from a sorted sequence.
 *
 *  Try to:
 *  1. write the code to compute b
 *  2. write the ensures clauses that specify the remove duplicate property
 *  3. prove the ensures. 
 *
 *  Notes: a[k] accesses element k of k for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0.. |a| - 1] is same as a.  
 */
method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures forall j, k::0 <= j < k < |b|  ==> b[j] < b[k]
    ensures forall j :: j in a ==> j in b
    ensures sorted(b)
{
    if |a| == 0 {
        b := [] ;
    } else 
    {
        var last := a[0];
        b := [a[0]];

        var index := 1;
        while index < |a|
            decreases |a| - index
            invariant index <= |a|;
            invariant |b| >= 1;
            invariant b[|b| - 1] == last;
            invariant forall j, k::0 <= j < k < |b|  ==> b[j] < b[k];
            invariant last in a[..index];   // slide with operations on seq!
            invariant forall j :: j in a[..index] ==> j in b
        {
            if ( a[index] != last ) { 
                b := b + [a[index]];
                last := a[index];
            }
            index := index + 1;
        }
    }
}

/**
 *  Dafny compiles the Main method if it finds one.
 */
method Main() {
    var r := find([], 1);   //assume an alias to call dafny!!
    print r, "\n";

    r := find([0,3,5,7], 5);   //assume an alias to call dafny!!
    print r, "\n";

    var s := unique([0,1,3,3,5,5,7]);
    print s, "\n";
    
}

lemma foo(i : int) 
{
    assert(  exists k :: ((0 <= k < i ==> false ) ==> true)) ;
}

/**
 *  Example 3.
 *
 *  Remove duplicates from a sorted sequence.
 *
 *  Try to:
 *  1. write the code to compute b
 *  2. write the ensures clauses that specify the remove duplicates properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of k for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0.. |a| - 1] is same as a.  
 */
method unique2(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    // every element of b should be in a
    ensures forall k :: 0 <= k < |b| ==> b[k] in a
    // conversely every element of a should also be in b
    ensures forall k :: 0 <= k < |a| ==> a[k] in b
    // result is sorted as well
    ensures sorted(b)
    // uniqueness. no element appears in its suffix-subsequence.
    ensures forall k :: 0 <= k < |b|-1 ==> b[k] !in b[k+1..]
{
    if(|a| == 0) {
        return [];
    }

    // If the control reaches here, a is guaranteed to be of size >= 1
    var i := 1;
    b := [a[0]];

    while i < |a| 
        decreases |a| - i
        invariant 1 <= i <= |a|
        invariant sorted(b)
        invariant forall k :: 0 <= k < i ==> a[k] in b
        invariant forall k :: 0 <= k < |b| ==> b[k] in a
        invariant forall k :: (0 <= k < |b| - 1 ==> b[k] !in b[k+1..])
        invariant a[i-1] == b[|b|-1];
    {
        if(a[i] != a[i-1]) {
            b := b + [a[i]];
        }
        i := i + 1;
    }
}