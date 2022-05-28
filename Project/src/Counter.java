/**
 * CVS 2021-22 Project- Task 1
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */

 /*@ predicate CounterInv(Counter c; int a, int l, boolean o) = c.val |-> a 
                                                            &*& c.limit |-> l 
                                                            &*& c.overflow |-> o
                                                            &*& a >= 0 &*& l > 0;
@*/

public class Counter {

    private int val;
    private int limit;
    private boolean overflow;

    public Counter(int val, int limit) 
        //@ requires val>=0 &*& limit>0;
        //@ ensures CounterInv(this, val, limit, false);
    {
       
        // TODO rever
        this.limit = limit;
        this.val = val;
        overflow = false;
    }

    public int getVal() 
        //@ requires CounterInv(this, ?a, ?l, ?o);
        //@ ensures CounterInv(this, a, l, o) &*& result ==  a % l &*& result < l &*& result >= 0;
    {
      
        // TODO rever
        return val % limit;
    }

    public int getLimit() 
        //@ requires CounterInv(this, _ , ?l, _);
        //@ ensures CounterInv(this, _ , l, _) &*& result == l;
    {

        // TODO rever
        return limit;
    }

    public void incr(int v) 
        //@ requires CounterInv(this, ?a, ?l, ?o) &*& v >= 0;
        //@ ensures CounterInv(this, a + v, _ , o || (a + v >= l));
    {
        // TODO rever
        if (val + v >= limit) {
            overflow = true;
        } 
        val += v;
    }

    public void decr(int v) 
        //@ requires CounterInv(this, ?a, ?l, ?o) &*& v >= 0;
        //@ ensures CounterInv(this, ((a - v < 0) ? 0 : a - v), _ , o || (a - v < 0));
    {
        // TODO rever
        if (val - v < 0) {
            val = 0;
            //@ open CounterInv(this, _, _, o);
            overflow = true;
            //@ close CounterInv(this, _, _, true);
        } else {
            val -= v;
        }
    }

}
