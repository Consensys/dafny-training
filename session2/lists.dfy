// Dafny 2.3.0.10506
// Command Line Options: /dprint:verified-calculations/list-formatted.dfy /compile:0 verified-calculations/list.dfy
// list.dfy

/**
 *  Lists.
 */
datatype List<T> = Nil | Cons(T, List<T>)

/**
 *  Length of a list.
 */
function length<T>(xs: List<T>): nat
{
    match xs
        case Nil => 0

        case Cons(x, xrest) => 1 + length(xrest)
}

/**
 *  Existence of lists of length 1.
 */
lemma existsListOfLengthOneNat()
  ensures exists l: List<nat> :: length(l) == 1
{
  var l: List<nat>;
  l := Cons(496, Nil);
  assert length(l) == 1;
}

/**
 *  Same as above.
 */
lemma witnessLengthOneNat()
  ensures length(Cons(496, Nil)) == 1
{
}

/**
 *  Example of a lemma without a proof ...
 *  dangerous! This one states that false is ... true.
 */
lemma foo1()
  ensures false

/**
 *  Existence of lists of arbitrary length.
 *  Demonstrate how to prove existnetial properties.
 */
lemma existsListOfArbitraryLength<T>(n: nat)
  ensures exists l: List<T> :: length(l) == n
{
  if n == 0 {
    var x: List<T> := Nil;
    assert length(x) == 0;
  } else {
    existsListOfArbitraryLength<T>(n - 1);
    var xs: List<T> :| length(xs) == n - 1;
    var t: T;
    assert length(Cons(t, xs)) == n;
  }
}

/**
 *  Append an element to a list.
 */
function append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
    case Nil => ys

    case Cons(x, xrest) => Cons(x, append(xrest, ys))
}

/**
 *  Reverse of a list.
 */
function reverse<T>(xs: List<T>): List<T>
{
  match xs
    case Nil => Nil

    case Cons(x, xrest) => append(reverse(xrest), Cons(x, Nil))
}


/**
 *  Nil is neutral element for appemd.
 */

lemma appendNilNeutral<T>(l: List<T>)
  ensures append(l, Nil) == l == append(Nil, l)
{
}

/**
 *  Appemd is associative
 */
lemma append2<T>(l1: List<T>, l2: List<T>, l3: List<T>)
  ensures append(append(l1, l2), l3) == append(l1, append(l2, l3))
{
}

/**
 *  Reverse is involutive.
 */
lemma reverseInvolutive<T>(l: List<T>)
  ensures reverse(reverse(l)) == l
{
  match l
  case Nil =>

  case Cons(hd, tl) =>
    calc {
      reverse(reverse(l));
    ==
      reverse(append(reverse(tl), Cons(hd, Nil)));
    ==
      {
        LemmaReverseAppendDistrib(reverse(tl), Cons(hd, Nil));
      }
      append(reverse(Cons(hd, Nil)), reverse(reverse(tl)));
    ==
      {
        reverseInvolutive(tl);
      }
      append(reverse(Cons(hd, Nil)), tl);
    ==
      append(Cons(hd, Nil), tl);
    ==
      l;
    }
}

/**
 *  A useful lemma combining reverse and append.
 *  Distribution.
 */
lemma LemmaReverseAppendDistrib<T>(l1: List<T>, l2: List<T>)
  ensures reverse(append(l1, l2)) == append(reverse(l2), reverse(l1))
{
  match l1
  case Nil =>
    calc {
      reverse(append(l1, l2)); // line<0>
    == // S<0>
      reverse(append(Nil, l2)); // line<1>
    ==
      reverse(l2);
    ==
      {
        appendNilNeutral(reverse(l2));
      }
      append(reverse(l2), Nil);
    }
  case Cons(h1, t1) =>
    calc {
      reverse(append(l1, l2));
    ==
      reverse(append(Cons(h1, t1), l2));
    ==
      reverse(Cons(h1, append(t1, l2)));
    ==
      append(reverse(append(t1, l2)), Cons(h1, Nil));
    ==
      append(append(reverse(l2), reverse(t1)), Cons(h1, Nil));
    ==
      {
        append2(reverse(l2), reverse(t1), Cons(h1, Nil));
      }
      append(reverse(l2), append(reverse(t1), Cons(h1, Nil)));
    ==
      append(reverse(l2), reverse(Cons(h1, t1))) ;
    }
}
