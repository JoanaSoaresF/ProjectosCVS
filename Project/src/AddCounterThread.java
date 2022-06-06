
/*@ predicate AddThreadInv(AddCounterThread t;) = t.seq |-> ?s &*& s != null
&*& [_]CCSeqInv(s)
;@*/



class AddCounterThread implements Runnable {
    //@ predicate pre() = AddThreadInv(this);
    //@ predicate post() = true;

    public CCSeq seq;
 

    public AddCounterThread(CCSeq seq)
    //@ requires seq != null &*& [_]CCSeqInv(seq); 
    //@ ensures AddThreadInv(this); 
    {
        this.seq = seq;
    }

    
    public void run()
    //@ requires pre(); 
    //@ ensures post();
    {
        //@ open pre();
        int c = seq.addCounter(100);
        while(true) 
        //@ invariant AddThreadInv(this);
        {
            seq.incr(c, 10);
            seq.decr(c, 10);
        }
        //@ close pos();
       
    }
}