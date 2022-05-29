/**
 * CVS 2021-22 Project- Task 1
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */

 /*@ predicate CounterInv(Counter c; int a, int l, boolean o) = c.val |-> a 
                                                            &*& c.limit |-> l 
                                                            &*& c.overflow |-> o
                                                            &*& a >= 0 &*& l > 0
                                                            &*& (a >= l) ? o == true : true;
@*/

public class Counter {

    protected int val;
    protected int limit;
    private boolean overflow;

    public Counter(int val, int limit) 
        //@ requires val >= 0 &*& limit > 0 &*& val < limit;
        //@ ensures CounterInv(this, val, limit, false);
    {
        this.limit = limit;
        this.val = val;
        overflow = false;
    }

    public int getVal() 
        //@ requires CounterInv(this, ?a, ?l, ?o);
        //@ ensures CounterInv(this, a, l, o) &*& result ==  a % l;
    {
        return val % limit;
    }

    public int getLimit() 
        //@ requires CounterInv(this, _ , ?l, _);
        //@ ensures CounterInv(this, _ , l, _) &*& result == l;
    {
        return limit;
    }

    public void incr(int v) 
        //@ requires CounterInv(this, ?a, ?l, ?o) &*& v >= 0;
        //@ ensures CounterInv(this, a + v, l , o || (a + v >= l));
    {
        if (val + v >= limit) {
            overflow = true;
        } 
        val += v;
    }

    public void decr(int v) 
        //@ requires CounterInv(this, ?a, ?l , ?o) &*& v >= 0;
        //@ ensures CounterInv(this, ((a - v < 0) ? 0 : a - v), l , o || (a - v < 0));
    {
        if (val - v < 0) {
            val = 0;
            overflow = true;
        } else {
            val -= v;
        }
    }

}
