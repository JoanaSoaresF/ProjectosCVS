class RemoveCounterThread implements Runnable {

    public CCSeq seq;
    //TODO
    //@ predicate pre() = [?f]CCSeqInv(seq);
    //@ predicate post() = true;

    public RemoveCounterThread(CCSeq seq)
    //@ requires seq != null &*& [f]CCSeqInv(seq); 
    //@ ensures CCSeqInv(seq); 
    {
        this.seq = seq;
    }

    public void run()
    //@ requires pre(); 
    //@ ensures post();
    {
        //TODO
        while (true)
        //@ invariant CCSeqInv(seq);
        {
                int c = seq.addCounter(100);
                seq.incr(c, 10);
                seq.decr(c, 10);
            
        }
    }
}