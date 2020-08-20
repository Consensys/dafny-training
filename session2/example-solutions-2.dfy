
/**
 *  Skeleton Dafny programs for session 2 of training.
 */

function method powerOf2(n: nat) : nat //   if no main do not se method.
    ensures powerOf2(n) >= 1  //    show that during the training!!
    decreases n
{
    if n == 0 then 
        1
    else 
        2 * powerOf2(n - 1)
}

/**
 *  Some lemmas about powerOf2
 *  Dafny can prove this lemma automatically, but
 *  we can also provide a proof, and in that case, it will check it.
 */
lemma sumSamePowerOf2(n: nat)
    ensures powerOf2(n) + powerOf2(n) == 2 * powerOf2(n)
{
    if n == 0 {
        //  Thanks Dafny.
        //  expand that during training and then ask them to do induction
        calc {
            powerOf2(n) + powerOf2(n);
            ==
            powerOf2(0) + powerOf2(0);
            == calc {
                powerOf2(0);
                ==
                1;
            }
            1 + 1;
            == 
            2 * 1;
            ==
            2 * powerOf2(0);
        }
    } else {
        //  Induction on n - 1 as n >= 1
        calc {
            powerOf2(n) + powerOf2(n);
            ==
            2 * powerOf2(n - 1) + 2 * powerOf2(n - 1);
            ==
            2 * ( powerOf2(n - 1) + powerOf2(n - 1));
            //  Induction on n - 1
            == {sumSamePowerOf2(n - 1);  }
            2 * ( 2 * powerOf2(n - 1));
            == //   def of power2(n)
            2 * powerOf2(n);
        }
    }
}

//  ask them to do both
lemma monotonicPowerOf2(n: nat, m: nat)
    requires n <= m
    ensures powerOf2(n) <= powerOf2(m)
{
    if n == 0 {
        //  Thanks Dafny.
        calc {
            powerOf2(n);
            ==
            powerOf2(0);
            ==
            1;
            <=
            powerOf2(m);
        }
    } else {
        //  Induction on n - 1 as n >= 1
        calc {
            powerOf2(n);
            ==  //  def of powerOf2(n)
            2 * powerOf2(n - 1);
            <= { monotonicPowerOf2(n - 1, m - 1)  ;} 
            2 * powerOf2(m - 1);
            ==
            powerOf2(m);
        }
    }
}

//  exercise: ask them to do both
lemma {:induction n} addPowerOf2(n: nat, m : nat)
    ensures powerOf2(n) * powerOf2(m) == powerOf2(n + m)  
{
    //  @todo: write the proof instead of assuming it.
    // assume(powerOf2(n) * powerOf2(m) == powerOf2(n + m) );
   if n == 0 {
    //    calc == {
    //        powerOf2(n) * powerOf2(m);
    //        powerOf2(0) * powerOf2(m);
    //        1 * powerOf2(m);
    //        powerOf2(m);
    //        powerOf2(0 + m);
    //        powerOf2(n + m);
    //    }
   } else {
       //  n >= 1, induction on n
       //   show that the only thing thatDafny does not guess
       //   is what the induction is on.
       //    as a result, if we indicate what induction should be on,
       //   the proof goes through automatically.
    //    addPowerOf2(n - 1, m);
    //    calc == {
    //     //    powerOf2(n) * powerOf2(m);
    //        2 * powerOf2(n - 1) * powerOf2(m);
    //        //   induction on (n - 1, m)
    //        { addPowerOf2(n - 1, m); }
    //        2 * powerOf2(n - 1 + m);
    //        //   def of powerOf2
    //     //    powerOf2(n - 1 + m + 1);
    //     //    powerOf2(n + m);
    //    }
   }
}

//  Tree examples 

/**
 *  Binary, non-empty trees.
 */
datatype Tree = 
        Leaf
    |   Node(left: Tree, right: Tree)

/**
 *  Height of a tree.
 *  
 *  @param  root    The root of the tree.
 *  @returns        The height of the tree rooted at `root`.
 */
function height(root : Tree) : nat 
    ensures height(root) >= 1
    decreases root
{
    match root 
        case Leaf => 1
        case Node(lc, rc) => 1 + max(height(lc), height(rc))
}

/**
 *  Maximum of two non-negative integers.
 */
function method max(x: nat, y : nat) : nat 
{
    if x > y then 
        x
    else 
        y
}

/**
 *  The number of nodes in a tree.    .
 *
 *  @param  root    The root of the tree.
 *
 *  @return         The number of nodes (including leaves) in the tree.
 *  @note           Perform a in-order (left, node, right) traversal to
 *                  compute the result.
 */
function method nodesCount(root : Tree) : nat
    ensures nodesCount(root) >= 1
    decreases root
{
    match root 
        case Leaf => 1
        case Node(lc, rc) =>  1 + nodesCount(lc) + nodesCount(rc) 
}

/**
 *  The number of leaves in a tree.    .
 *
 *  @param  root    The root of the tree.
 *
 *  @return         The number of leaves in the tree.
 *  @note           Perform a in-order (left, node, right) traversal to
 *                  compute the result.
 */
function method leavesCount(root : Tree) : nat
    ensures leavesCount(root) >= 1
    decreases root
{
    match root 
        case Leaf => 1
        case Node(lc, rc) =>  leavesCount(lc) + leavesCount(rc) 
}

/**
 *  The number of nodes if less than 2^(height(root)) - 1
 */
lemma upperBoundForNodesCount(root : Tree)
    ensures nodesCount(root) <= powerOf2(height(root)) - 1
{
    if height(root) == 1 {
        //  
    } else {
        match root 
            case Node(lc, rc) =>
                //  show that some lines cna be commented out
                calc == {
                    // nodesCount(root);
                    1 + nodesCount(lc) + nodesCount(rc) ;
                    <= { upperBoundForNodesCount(rc); upperBoundForNodesCount(lc); }
                    1 + powerOf2(height(lc)) - 1 + powerOf2(height(rc)) - 1;
                    // powerOf2(height(lc)) +  powerOf2(height(rc)) - 1;
                    <= {    monotonicPowerOf2(height(lc), height(root) - 1) ;
                            monotonicPowerOf2(height(rc), height(root) - 1) ; 
                    }
                    powerOf2(height(root) - 1) + powerOf2(height(root) - 1) - 1;
                    { sumSamePowerOf2(height(root) - 1) ; }
                    // 2 *  powerOf2(height(root) - 1) - 1;
                    //  def of powerOf2
                    // powerOf2(height(root)) - 1;
                }
    }
}

/**
 *  The number of leaves is less than 2^(height(root) - 1) 
 */
lemma {:induction root} upperBoundForLeavesCount(root : Tree)
    ensures leavesCount(root) <= powerOf2(height(root) - 1) 
{
    // assume(leavesCount(root) <= powerOf2(height(root) - 1)); 
    if (height(root) > 1) {
        match root 
            case Node(lc, rc) =>
                //  first proof
                // upperBoundForLeavesCount(lc);
                // upperBoundForLeavesCount(rc);
                monotonicPowerOf2(height(lc), height(root) - 1) ;
                monotonicPowerOf2(height(rc), height(root) - 1) ; 
                // sumSamePowerOf2(height(root) - 1);
                //  second proof
                // calc == {
                //      leavesCount(root);
                //      leavesCount(lc) + leavesCount(rc);
                //      <= 
                //      powerOf2(height(lc) - 1) + powerOf2(height(rc) - 1);
                //      <= {    monotonicPowerOf2(height(lc), height(root) - 1) ;
                //             monotonicPowerOf2(height(rc), height(root) - 1) ; 
                //      }
                //      powerOf2(height(root) - 2) + powerOf2(height(root) - 2) ;
                //     { sumSamePowerOf2(height(root) - 1) ; }
                //      2 *  powerOf2(height(root) - 2);
                //     //  def of powerOf2
                //     powerOf2(height(root) - 1);
                // }
    }
}

//  If you want to to run the code, compile this file with:
//  dafny /noVerify /compile:4 yourPath/training2.dfy
/**
 *  Dafny compiles the Main method if it finds one in a file.
 */
method Main() {
    //  Example with powerOf2
    //  note: you need to have powerOf2 declared as a function method
    //  to be executable.
    var r := powerOf2(1);   
    print "powerOf2(1) is: ", r, "\n";

    var n:= 0;
    while n < 20 
        decreases 20 - n
    {
        var r := powerOf2(n);
        print "powerOf2(", n, ") is: ", r, "\n";
        n := n + 1;
    }   
}