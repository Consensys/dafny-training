/*
 * Copyright 2021 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */
 
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
    // assert i == n;
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
 *  Palidrome checker.
 *  Example 3.
 *
 *  Check whether a sequence of letters is a palindrom.
 *
 *  Try to:
 *  1. write the algorithm to determine whether a string is a palindrom
 *  2. write the ensures clauses that specify the palidrom properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of k for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0.. |a| - 1] is same as a.  
 */
method isPalindrome(a: seq<char>) returns (b: bool) 
    ensures b <==> (forall j:: 0 <= j < |a| / 2 ==> a[j] == a[|a| - 1 - j] )
{
    var i := 0;
    while i < |a| / 2 
        invariant 0 <= i <= |a|
        invariant forall j:: 0 <= j < i ==> a[j] == a[|a| - 1 - j]
    {
        if a[i] != a[|a| - 1 - i] {
            return false;
        } else {
            i := i + 1;
        }
    }
    return true;
}

/**
 *  Functional specification of palindrom.
 */
function isPalindrome1(a: seq<char>): bool 
    ensures isPalindrome1(a) <==> (forall j:: 0 <= j < |a| / 2 ==> a[j] == a[|a| - 1 - j] )
    decreases |a|
{
    if |a| <= 1 then 
        true
    else 
        assert(|a| >= 2);
        a[0] == a[|a| - 1] && isPalindrome1(a[1..|a| - 1])
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
    ensures forall j :: j in a <==> j in b
{
    if |a| == 0 {
        b := [] ;
    } else 
    {
        var last := a[0];
        b := [a[0]];

        var index := 1;
        while (index < |a|)
            decreases |a| - index
            invariant index <= |a|;
            invariant |b| >= 1;
            invariant b[|b| - 1] == last;
            invariant forall j, k::0 <= j < k < |b|  ==> b[j] < b[k];
            invariant last in a[..index];   // slide with operations on seq!
            invariant forall j :: j in a[..index] <==> j in b
            // invariant forall j :: j in a[..index] ==> j in b
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
    //  run find
    var r := find([], 1);   
    print r, "\n";

    r := find([0,3,5,7], 5);  
    print r, "\n";

   
    //  run palindrome
    var s1 := ['a'];
    var r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := [];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := ['a', 'b'];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := ['a', 'b', 'a'];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

   // run unique
    var i := [0,1,3,3,5,5,7];
    var s := unique(i);
    print "unique applied to ", i, " is ", s, "\n";

}

