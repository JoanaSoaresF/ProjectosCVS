/**
 * CVS 2021-22 Project- Task 1
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */

 /*@ predicate ValidLimit(unit a, int v; unit n) = v > 0 &*& n == unit;@*/


 /*@ predicate CounterP(unit y,Counter c; unit b) = c != null &*& CounterInv(c,?a, ?l, ?o) &*& b == unit; @*/
 
 /*@ predicate CounterSequenceInv(CounterSequence cs; int c, int n) = cs.sequence |-> ?s
                                &*& cs.capacity |-> c
                                &*& cs.nCounters |-> n
                                &*& n <= c
                                &*& s.length == c &*& c > 0
                                &*& s != null
                                &*& n >= 0 &*& n <= s.length
                                &*& array_slice_deep(s,0,n,CounterP, unit, _, _) 
                                &*& array_slice(s,n,c,?others) &*& all_eq(others, null) == true
                                
                                                        ;
 @*/

public class CounterSequence {

    private Counter[] sequence;
    private int capacity;
    private int nCounters;

    
    public CounterSequence(int cap) 
        //@ requires cap > 0;
        //@ ensures CounterSequenceInv(this, cap, 0);
    {
        sequence = new Counter[cap];
        capacity  = cap;
        nCounters = 0;
    }
   
    public CounterSequence(int[] arr) 
        //@ requires arr != null &*& arr.length > 0 &*& array_slice_deep(arr,0,arr.length,ValidLimit,unit,_,_);
        //@ ensures CounterSequenceInv(this, arr.length, arr.length);
    {
        capacity  = arr.length;
        sequence = new Counter[capacity];
        nCounters = 0;
        while(nCounters < capacity)
            /*@ invariant this.sequence |-> ?s &*& s != null 
            &*& this.nCounters |-> ?n &*& n >= 0 
            &*& this.capacity |-> ?cap &*& n <= cap
            &*& cap == s.length &*& cap == arr.length
            &*& array_slice_deep(arr,0,arr.length,ValidLimit,unit,_,_)
            &*& array_slice_deep(s, 0, n, CounterP, unit, _, _) 
            &*& array_slice(s, n, cap, ?elems) &*& all_eq(elems, null) == true
            ;@*/
        {
            Counter c = new Counter(0, arr[nCounters]);
            sequence[nCounters] = c;
            nCounters++;
         
        }
   
    }

    public int length() 
        //@ requires CounterSequenceInv(this , ?c, ?n);
        //@ ensures CounterSequenceInv(this , c, n) &*& result == n;
    {
        return nCounters;
    }

    public int capacity() 
        //@ requires CounterSequenceInv(this , ?c, ?n);
        //@ ensures CounterSequenceInv(this , c, n) &*& result == c;
    {
        return capacity;
    }

    public int getCounter(int i) 
        //@ requires CounterSequenceInv(this , ?c, ?n) &*& i >= 0 &*& i < n ;
        //@ ensures CounterSequenceInv(this , c, n) &*& result >= 0;
    { 
        int result = sequence[i].getVal();
    
        return result;
    }
    
   
    public int addCounter(int limit) 
        //@ requires CounterSequenceInv(this , ?c, ?n) &*& limit > 0 &*& n < c;
        /*@ ensures CounterSequenceInv(this , c, n + 1);@*/ 
    {

        Counter counter = new Counter(0, limit);
        
        sequence[nCounters] = counter;
        nCounters = nCounters + 1;
  
        return nCounters - 1;
    }


    public void remCounter(int pos)
        //@ requires CounterSequenceInv(this, ?c, ?n) &*& n >= 1 &*& pos >= 0 &*& pos < n;
        //@ ensures CounterSequenceInv(this, c, n - 1);
    
    {
        if(pos == nCounters - 1 ) {
            sequence[nCounters - 1] = null;
            nCounters -= 1;
        } else {
            sequence[pos] = sequence[nCounters - 1];
            sequence[nCounters - 1] = null;
            nCounters -= 1;
        }
    }

    public void remCounterPO(int pos) 
        //@ requires CounterSequenceInv(this, ?c, ?n) &*& n >= 1 &*& pos >= 0 &*& pos < n;
        //@ ensures CounterSequenceInv(this, c, n - 1);
    {
        int i = pos+1;
        //NOTE não é necessário alterar para o null
        //@ close CounterSequenceInv(this, c, n);
        while(i < nCounters)
        /*@ invariant 
        CounterSequenceInv(this, c, n)
        &*& i <= n &*& i >= pos +1
        ;@*/ 
        // @ decreases nCounters - i;
        {
            Counter aux = sequence[i];
            sequence[i-1] = aux;
            Counter dummy = new Counter(0, 1);
            sequence[i] = dummy;
            i = i+1;       
        }
        sequence[--nCounters] = null;
    }

    public void increment(int i, int val) 
        //@ requires CounterSequenceInv(this , ?c, ?n) &*& i >= 0 &*& i < n &*& val >= 0;
        //@ ensures CounterSequenceInv(this , c, n);
    {
        sequence[i].incr(val);
    }

    public void decrement(int i, int val) 
        //@ requires CounterSequenceInv(this , ?c, ?n) &*& i >= 0 &*& i < n &*& val >= 0;
        //@ ensures CounterSequenceInv(this , c, n);
    {
        sequence[i].decr(val);
    }
}
