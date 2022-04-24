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

    /*Initializes an interval tree for a sequence of n elements whose values are 0. */ 
    constructor(n: int) 
    //TODO especificação
    requires n > 0 
    ensures leaves == n {
        //TODO
    }
    //Updates the i-th sequence element (0-based) by v 
    method update(i: int,v: int) 
    //TODO especificação
    requires 0 <= i < leaves {
        //TODO
    }

    //Ranged sum over interval [a,b[ 
    method query(a: int,b: int) returns (r: int) 
    //TODO especificação
    requires 0 <= a <= b <= leaves 
    ensures r == rsum(a,b) {
        //TODO
    }

    predicate Valid() {
        //TODO
        true
    }

    //Sum of elements over range [a,b[ 
    function rsum(a: int,b: int) : int 
    requires Valid() 
    decreases b-a 
    requires 0 <= a <= leaves && 0 <= b <= leaves 
    reads //TODO reads 
    {
        if b <= a then 0 else get(b-1) + rsum(a, b-1) 
    }


    predicate ValidSize() 
    reads //TODO reads
    {
    tree.Length == 2*leaves-1 
    }


    /*ith element of the sequence, through the array-based representation*/ 
    function get(i: int) : int 
    requires 0 <= i < leaves && ValidSize() 
    reads // TODO reads
    {
        tree[i+leaves-1]
    }


    function sumArr(a: int,b: int) : int 
    requires Valid() 
    requires 0 <= a <= tree.Length && 0 <= b <= tree.Length 
    reads //TODO reads
    {
        if b <= a then 0 else tree[b-1] + sumArr(a,b-1) 
    }

    lemma shift(a: int,b: int,c: int) 
    requires Valid() && 0 <= c <= leaves-1 
    requires 0 <= a <= leaves && 0 <= b <= leaves 
    requires forall i:: a <= i < b ==> get(i) == tree[i+c] 
    // requires ∀ i • a ≤ i < b =⇒ get(i) = tree[i+c] 
    ensures rsum(a,b) == sumArr(a + c, b + c) 
    decreases b-a {
        //TODO
     }

    lemma crucial(ra: int,rb: int) 
    requires 0 <= ra <= rb && 2*rb < tree.Length && Valid() 
    ensures sumArr(ra,rb) == sumArr(2*ra+1,2*rb+1){
        //TODO
    }


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
        //TODO
        0
    }

}