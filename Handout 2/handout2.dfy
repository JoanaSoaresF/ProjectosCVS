/**
CVS 2021-22 Handout 2
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

class IntervalTree {

    //The actual tree 
    var tree: array<int>

    /*The number of leaves in the tree (i.e. the number of elements in the sequence). */ 
    ghost var leaves: int

    ghost var s : seq<int> // for task tree

    /*Initializes an interval tree for a sequence of n elements whose values are 0. */ 
    constructor(n: int) 
    requires n > 0 
    ensures leaves == n
    ensures Valid()
    ensures forall i :: 0 <= i < n ==> get(i) == 0
    {
        tree := new int[2 * n - 1] ( i => 0); 
        leaves := n;
    }

    function sumChildren(i : int, t : array<int>) : int
        requires 0 <= i < t.Length/2 - 1
        reads t
    {
        t[2*i+1] + t[2*i+2]
    }

    //Updates the i-th sequence element (0-based) by v 
    method update(i: int,v: int) 
    //TODO especificação
    requires 0 <= i < leaves
    requires Valid()
    modifies `tree, tree
    ensures Valid()
    ensures forall j:: 0 <= j < leaves ==> if (j != i) then get(j) == old(get(j)) else get(j) == old(get(j)) + v
    // ensures forall k:: 0<= k < tree.Length/2 ==> tree[k] == tree[2*k+1] + tree[2*k+2]
    {
        var pos := tree.Length/2 + i;
        tree[pos] := tree[pos] + v;
        while(pos != 0) 
            invariant 0 <= pos <= tree.Length/2 + i
            //invariant forall k:: 0<= k < tree.Length/2 - 1 ==> 
            //    if (k>=pos) then tree[k] == old(tree[2*k+1]) + old(tree[2*k+2]) + v
            //    else tree[k] == old(tree[2*k+1]) + old(tree[2*k+2])
            //invariant forall k:: 0<= k < pos ==> tree[k] == old(tree[2*k+1]) + old(tree[2*k+2])
            invariant forall k:: 0 <= k < tree.Length/2 - 1 ==> if k == pos*2+1 || k == pos*2+2
                                                        then sumChildren(k, tree) - v == tree[k]
                                                        else tree[k] == sumChildren(k, tree) 
        {
            pos := (pos-1)/2;
            tree[pos] := tree[pos] + v;
        }    
    }

    //Ranged sum over interval [a,b[ 
    method query(a: int,b: int) returns (r: int) 
    //TODO especificação
    requires 0 <= a <= b <= leaves 
    ensures r == rsum(a,b) 
    //ATTENTION - rever
    requires Valid()
    ensures Valid()
    {
    
        var ra := tree.Length/2 + a;
        var rb := tree.Length/2 + b;
        r := 0;
        while(ra < rb)
        //TODO invariantes
        invariant 0 <= ra <= tree.Length/2 + a;
        invariant 0 <= rb <= tree.Length/2 + b;
        invariant r == sumArr(ra, rb);
        decreases ra, rb;
        
        {
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

        }
    }

    predicate Valid() 
    reads `tree, `leaves, tree
    {
        //TODO
        ValidSize() 
        && 
        forall i :: 0 <= i < leaves-1 ==> tree[i] == tree[2*i+1] + tree[2*i+2]
        
        //Task tree
        // && |s| = leaves 
        // && tree[0] = sum(s)
        // && forall i:: 0 <= i < leaves ==> s[i] == get(i)
    }

    //Sum of elements over range [a,b[ 
    function rsum(a: int,b: int) : int 
    requires Valid() 
    decreases b-a 
    requires 0 <= a <= leaves && 0 <= b <= leaves 
    reads `tree,`leaves, tree //ATTENTION rever reads
    {
        if b <= a then 0 else get(b-1) + rsum(a, b-1) 
    }


    predicate ValidSize() 
    reads `tree, `leaves //ATTENTION rever reads
    {
        tree.Length == 2*leaves-1 
    }


    /*ith element of the sequence, through the array-based representation*/ 
    function get(i: int) : int 
    requires 0 <= i < leaves && ValidSize() 
    reads tree, `leaves, `tree //ATTENTION rever reads
    {
        tree[i+leaves-1]
    }


    function sumArr(a: int,b: int) : int 
    requires Valid() 
    requires 0 <= a <= tree.Length && 0 <= b <= tree.Length 
    reads tree, `tree //ATTENTION rever reads
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
    // TODO lemma shift


    lemma crucial(ra: int,rb: int) 
    requires 0 <= ra <= rb && 2*rb < tree.Length && Valid() 
    ensures sumArr(ra,rb) == sumArr(2*ra+1,2*rb+1)
    //TODO lemma crucial


    lemma sumArrSwap(ra: int,rb: int) 
    requires Valid() 
    requires 0 <= ra < rb && 0 <= rb <= tree.Length 
    ensures sumArr(ra,rb) == tree[ra]+sumArr(ra+1,rb){
        //TODO
    }

    lemma sum_zero(s: seq<int>) 
    requires forall i:: 0 <= i < |s| ==> s[i] == 0 
    ensures sum(s) == 0{
        //TODO
    }


    lemma sum_elem(s: seq<int>,x: int,p: int) 
    requires 0 <= p < |s| 
    ensures x+sum(s) == sum(s[p := s[p]+x]){
        //TODO
    }


    function sum(s: seq<int>) :int {
       if |s| == 0 then 0 else s[0]+sum(s[1..])
    }

}