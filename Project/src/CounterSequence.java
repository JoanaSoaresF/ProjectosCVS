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

 /* @ fixpoint boolean orderPreserved(list<int> oldList, list<int> newList, int i, int pos)
{
    switch (i) {
        case pos<= i: return true;
        case pos<= i: return nth(pos, newList) == nth(pos + 1, oldList) 
                && orderPreserved(oldList, newList, i, pos - 1);  

    }
}
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
        //@ ensures CounterSequenceInv(this, _ , ?n, ?c) &*& array_slice(arr, 0, arr.length, _) &*& n == arr.length &*& c==arr.length;
    {
        sequence = new Counter[arr.length];
        capacity  = arr.length;
        nCounters = 0;
        for(int i = 0; i < arr.length; i++)
            /*@ invariant this.sequence |-> ?s &*& s != null &*& i>=0 &*& i<= arr.length &*& i<= s.length 
            &*& array_slice_deep(arr,0,arr.length,ValidLimit,unit,_,_) 
            &*& array_slice_deep(s, 0, i, CounterP, unit, _, _) 
            &*& array_slice(s, i, s.length, ?elems) &*& all_eq(elems, null) == true
            ;@*/
        {
            Counter c = new Counter(0, arr[i]);
            //FIXME No matching heap chunks: java.lang.array_element<class Counter>(s, i, _)
            sequence[i] = c;
            nCounters++;
        
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
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& i >= 0 &*& i < n  &*& s[i] |-> ?counter &*& counter != null &*& CounterInv(counter, ?v, ?l, _);
        /*@ ensures CounterSequenceInv(this, s , c, n) &*& result == v % l;@*/
    { 
        //ATTENTION pré condições? Parece que não passa sempre, se puser &*& n == -5 na pos condição dá mal;
        int result = sequence[i].getVal();
    
        return result;
    }
    

    public int addCounter(int limit) 
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& limit > 0 &*& n < c;
        /*@ ensures CounterSequenceInv(this, s , c, n + 1) 
                                &*& s[n] |-> ?counter &*& CounterP(_, counter, _)
                                &*& result == n 
                                &*& counter.val == 0
                                &*& counter.limit == limit
                                &*& counter.overflow == false
                                ;@*/
    {
        //FIXME No matching heap chunks: java.lang.array_element<class Counter>(s, n, _)
        Counter counter = new Counter(0, limit);
        sequence[nCounters++] = counter;
        return nCounters - 1;
    }

    public void remCounter(int pos)
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& n >= 1 &*& pos >= 0 &*& pos < n &*& s[n-1] |-> ?nc &*& s[pos] |-> ?counter &*& counter != null &*& CounterInv(counter, ?v, ?l, _) ;
        /*@ ensures CounterSequenceInv(this, s , c, n - 1) &*& s[pos] |-> ? counterPos
        &*& (pos == n - 1) ? counterPos == null : counterPos == nc
        ;@*/
    {
        //FIXME (Cannot prove counter = 0
        if(pos == nCounters - 1 ) {

            sequence[nCounters - 1] = null;
            nCounters -= 1;
        } else {
            sequence[pos] = sequence[--nCounters];
            sequence[nCounters] = null;

        }
      
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
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& i >= 0 &*& i < n &*& val >= 0 &*& s[i] |-> ?counter &*& counter != null &*& CounterInv(counter, ?v, ?l, _);
        //@ ensures CounterSequenceInv(this, s , c, n) &*&  counter.val |-> ?newVal &*& newVal == v + val;
    {
        sequence[i].incr(val);
    }

    public void decrement(int i, int val) 
        //@ requires CounterSequenceInv(this, ?s , ?c, ?n) &*& i >= 0 &*& i < n &*& val >= 0 &*& s[i] |-> ?counter &*& counter != null &*& CounterInv(counter, ?v, ?l, _);
        //@ ensures CounterSequenceInv(this, s , c, n) &*& counter.val |-> ?newVal &*& (v - val > 0 ) ?  newVal == v - val : newVal == 0;
    {
        sequence[i].decr(val);
    }
}
