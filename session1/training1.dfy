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

/**
 *  Example 0.a.
 *  Counter-example generation.
 */
method abs (x: int) returns (y : int)
    ensures true; 
{
    if (x < 0) {
        y := -x;
    } else {
        y :=  x;
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
requires true;
ensures true;
{
    var r : int;
    if ( x > y ) {
        r := 0;
    } else {
        r := 1;
    }
    m := r;
    //  can use return r instead
    // return m;
}

/**
 *  Example 1.
 *  
 *  Try to prove 
 *  1. the final assert statement (uncomment and you may need to strengthen pre).
 *  2. termination, propose a decrease clause (to replace *)
 */
method ex1 (n: int)
    requires true
    ensures true
    decreases *
{
    var i := 0;
    while (i < n)
        invariant true;
        decreases *;    //  do not check termination
    {
        i := i + 1;
    }
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
requires true;
ensures true
{
    index := 0;
    while (index < |a|)
        invariant true ;
        {
            if ( a[index] == key ) { 
                return 0;
            }
            index := index + 2;
        }
    index := -10;
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
 *  2. write the ensures clauses that specify the remove duplicates properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of k for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0.. |a| - 1] is same as a.  
 */
method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures true
{
  return a;
}

/**
 *  Dafny compiles the Main method if it finds one in a file.
 */
method Main() {
    var r := find([], 1);   
    print r, "\n";

    r := find([0,3,5,7], 5);  
    print r, "\n";

    var s := unique([0,1,3,3,5,5,7]);
    print s, "\n";
    
}

