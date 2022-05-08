/**
CVS 2021-22 Handout 2 - Task 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

class IntervalTree {

    //The actual tree 
    var tree: array<int>;

    /*The number of leaves in the tree (i.e. the number of elements in the sequence). */ 
    ghost var leaves: int;

    ghost var Repr: set<object>;

    predicate ValidSize() 
        reads this, `tree
    {
        this in Repr && tree in Repr && tree.Length == 2*leaves-1 
    }

    predicate Valid() 
        reads this, tree
    {
        this in Repr 
        && tree in Repr 
        &&
        ValidSize() 
        && 
        forall i :: 0 <= i < leaves - 1 ==> tree[i] == tree[2*i+1] + tree[2*i+2]
        
        
        //Task tree
        // && |s| = leaves 
        // && tree[0] = sum(s)
        // && forall i:: 0 <= i < leaves ==> s[i] == get(i)
    }

    /*Initializes an interval tree for a sequence of n elements whose values are 0. */ 
    constructor(n: int) 
        requires n > 0 
        ensures leaves == n 
        ensures Valid()
        ensures forall i :: 0 <= i < n ==> get(i) == 0
        ensures fresh(Repr - {this})
    {
        // Repr := {this};
        tree := new int[2 * n - 1] ( i => 0); 
        leaves := n;
        Repr := {this};
        Repr := Repr + {this, tree};
    }

    function treeSize() : int 
        reads this
    {
        tree.Length
    }

    //Updates the i-th sequence element (0-based) by v 
    method update(i: int,v: int) 
        modifies Repr
        requires 0 <= i < leaves
        requires Valid()
        ensures Valid() 
        ensures fresh(Repr - old(Repr)) 
        ensures treeSize() == old(treeSize())
        ensures forall j:: (0 <= j < leaves ) ==> if (j != i) 
                                            then get(j) == old(get(j)) 
                                            else get(j) == old(get(j)) + v
    {
        var pos := tree.Length/2 + i; 
        tree[pos] := tree[pos] + v;
        
        // assert pos == i + leaves - 1;
        
        while(pos > 0)
            decreases pos 
            invariant old(tree) == tree && ValidSize() && fresh(Repr - old(Repr))
            invariant 0 <= pos <= tree.Length/2 + i
            invariant forall j:: 0 <= j < leaves ==> if (j != i) 
                                        then get(j) == old(get(j)) 
                                        else get(j) == old(get(j)) + v       
            invariant forall k:: 0 <= k <  tree.Length / 2 ==> if k == (pos - 1) / 2
                                                    then tree[k] == tree[2*k+1] + tree[2*k+2] - v 
                                                    else tree[k] == tree[2*k+1] + tree[2*k+2]
            //invariant forall k:: 0 <= k <  tree.Length / 2 ==> tree[k] == tree[2*k+1] + tree[2*k+2] - if (k == (pos - 1) / 2) then v else 0 
        {
            pos := (pos-1)/2;  
            tree[pos] := tree[pos] + v;
        }
        
        
    }

    //Ranged sum over interval [a,b[ 
    method query(a: int,b: int) returns (r: int) 
        requires 0 <= a <= b <= leaves
        requires Valid()
        ensures r == rsum(a,b) 
        ensures Valid() && fresh(Repr - old(Repr))
    {
    
        var ra := tree.Length/2 + a;
        var rb := tree.Length/2 + b;
        r := 0;
        
        shift(a, b, leaves-1);
       
        while(ra < rb)
            invariant 0 <= ra <= tree.Length/2 + a;
            invariant 0 <= rb <= tree.Length/2 + b;
            invariant r + sumArr(ra,rb) == rsum(a,b)
            decreases ra, rb;
        {
            sumArrSwap(ra,rb);
        
            //If ra is rigth child we add the array value
            if(ra % 2 == 0) {
                r := r + tree[ra];
            }
            //move up to ra parent
            ra := ra/2;

            // if rb is a right-child, since the interval is open on its upper-bound, we must include the value at position rb-1 in our sum because its node must be a leftchild.
            if(rb % 2 == 0) {
                r := r + tree[rb-1];
            }

            //move up to rb parent
            rb := (rb-1)/2;

            crucial(ra, rb);

        }
    }
    
    /*ith element of the sequence, through the array-based representation*/ 
    function get(i: int) : int 
        requires 0 <= i < leaves 
        requires ValidSize()
        reads this, Repr
    {
        tree[i+leaves-1]
    }

    //Sum of elements over range [a,b[ 
    function rsum(a: int,b: int) : int 
        requires Valid() 
        decreases b-a 
        requires 0 <= a <= leaves && 0 <= b <= leaves 
        reads this, Repr
    {
        if b <= a then 0 else get(b-1) + rsum(a, b-1) 
    }

    function sumArr(a: int,b: int) : int 
        requires Valid() 
        requires 0 <= a <= tree.Length && 0 <= b <= tree.Length 
        reads this, Repr
    {
        if b <= a then 0 else tree[b-1] + sumArr(a,b-1) 
    }

    lemma shift(a: int,b: int,c: int) 
        requires Valid() && 0 <= c <= leaves-1 
        requires 0 <= a <= leaves && 0 <= b <= leaves 
        requires forall i:: a <= i < b ==> get(i) == tree[i+c] 
        // requires ∀ i • a ≤ i < b =⇒ get(i) = tree[i+c] 
        ensures rsum(a,b) == sumArr(a + c, b + c) 
        decreases b-a
    {
        if(b > a) {
            shift(a,b-1, c);
        }
    }

    lemma crucial(ra: int,rb: int) 
        requires 0 <= ra <= rb && 2*rb < tree.Length && Valid() 
        ensures sumArr(ra,rb) == sumArr(2*ra+1,2*rb+1)
    {
        if(ra < rb){
            crucial(ra, rb-1);
        }

    }

    lemma sumArrSwap(ra: int,rb: int) 
        requires Valid() 
        requires 0 <= ra < rb && 0 <= rb <= tree.Length 
        ensures sumArr(ra,rb) == tree[ra]+sumArr(ra+1,rb)
    {
         if(ra < rb-1){
            sumArrSwap(ra, rb-1);
        }
    }
}