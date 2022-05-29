/**
 * CVS 2021-22 Project- Task 1
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */

 /*@ predicate ValidLimit(unit a, int v; unit n) = v > 0 &*& n == unit;@*/


 /*@ predicate CounterP(unit y,Counter c; unit b) = c != null &*& CounterInv(c,?a, ?l, ?o) &*& b == unit; @*/
 
 /*@ predicate CounterSequenceInv(CounterSequence cs; Counter[] s, int c, int n) = cs.sequence |-> s
                                                        &*& cs.capacity |-> c
                                                        &*& cs.nCounters |-> n
                                                        &*& n <= c
                                                        &*& s != null
                                                        &*& n >= 0 &*& n <= s.length
                                                        &*& array_slice_deep(s,0,n,CounterP, unit, _, _) 
                                                        &*& array_slice(s,n,s.length,?others) &*& all_eq(others, null) == true
                                                       
                                                        ;
 @*/
public class CounterSequence {

    private Counter[] sequence;
    private int capacity;
    private int nCounters;

    
    public CounterSequence(int cap) 
        //@ requires cap > 0;
        //@ ensures CounterSequenceInv(this, _, cap, 0);
    {
        sequence = new Counter[cap];
        capacity  = cap;
        nCounters = 0;
    }
   
    public CounterSequence(int[] arr) 
        //@ requires arr != null &*& arr.length > 0 &*& array_slice_deep(arr,0,arr.length,ValidLimit,unit,_,_) ;
        //@ ensures CounterSequenceInv(this, _ , arr.length, arr.length) &*& array_slice(arr, 0, arr.length, _);
    {
        //TODO
        sequence = new Counter[arr.length];
        capacity  = arr.length;
        nCounters = 0;
        for(int i = 0; i < arr.length; i++)
            // invariant CounterSequenceInv(this, ?s , arr.length, i);
            /*@ invariant CounterSequenceInv(this, ?s , arr.length, i) &*& array_slice_deep(arr,0,arr.length,ValidLimit,unit,_,_) &*& i >= 0 &*& i < arr.length;
            @*/
        {
            Counter c = new Counter(0, arr[i]);
            sequence[i] = c;
            //FIXME No matching heap chunks: java.lang.array_element<class Counter>(s, i, _)

            // @ array_slice_deep_close(sequence, i, CounterP, unit);
           
        }
    }

    public int length() 
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n);
        //@ ensures CounterSequenceInv(this, s , c, n) &*& result == n;
    {
        return nCounters;
    }

    public int capacity() 
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n);
        //@ ensures CounterSequenceInv(this, s , c, n) &*& result == c;
    {
        return capacity;
    }

    // &*& result == s[i].val
    // &*& array_slice(s, 0, c ,?vs) &*& result == nth(i, vs).val
    public int getCounter(int i) 
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& i >= 0 &*& i < n  &*& array_slice(s, 0, c ,?vs);
        /*@ ensures CounterSequenceInv(this, s , c, n) &*& result == nth(i, vs).val;@*/
    { 
        //TODO
        //FIXME Target of method call might be null.

        return sequence[i].getVal();
    }

    public int addCounter(int limit) 
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& limit > 0 &*& n < c;
        /*@ ensures CounterSequenceInv(this, s , c, n + 1) 
                                &*& result == n 
                                &*& s[n].val == 0
                                &*& s[n].limit == limit;@*/
    {
        //TODO
        Counter c = new Counter(0, limit);
        sequence[nCounters++] = c;

        return nCounters - 1;
    }

    public void remCounter(int pos)
        // @ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& pos >= 0 &*& pos < n;
        // @ ensures CounterSequenceInv(this, s , c, n - 1);
    {
        // TODO
        sequence[pos] = sequence[--nCounters];
        sequence[nCounters] = null;
    }

    public void remCounterPO(int pos) 
        // @ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& pos >= 0 &*& pos < n;
        // @ ensures CounterSequenceInv(this, s , c, n - 1);
    {
        // TODO
        for(int i = pos; i < nCounters-1; i++){
            sequence[i] = sequence[i];
        }
        sequence[--nCounters] = null;
    }

    public void increment(int i, int val) 
        // @ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& i >= 0 &*& i < n;
        // @ ensures CounterSequenceInv(this, s , c, n);
    {
        // TODO
        sequence[i].incr(val);
    }

    public void decrement(int i, int val) 
        // @ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& i >= 0 &*& i < n;
        // @ ensures CounterSequenceInv(this, s , c, n);
    {
        // TODO
        sequence[i].decr(val);
    }
}
