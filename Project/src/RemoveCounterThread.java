/**
 * CVS 2021-22 Project- Task 2
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */

/*@ predicate RemoveThreadInv(RemoveCounterThread t;) = t.seq |-> ?s &*& s != null
&*& [_]CCSeqInv(s)
;@*/

class RemoveCounterThread implements Runnable {

    public CCSeq seq;
    //TODO corrigir thread
    //@ predicate pre() = RemoveThreadInv(this);
    //@ predicate post() = true;

    public RemoveCounterThread(CCSeq seq)
    //@ requires seq != null &*& [_]CCSeqInv(seq); 
    //@ ensures RemoveThreadInv(this); 
    {
        this.seq = seq;
    }

    public void run() 
    //@ requires [_]System_out(?s) &*& pre(); 
    //@ ensures post();
    {
        //QUESTION
        //FIXME No matching heap chunks: [_]java.lang.System_out(_)
        //TODO por parametro no contrutor para que counter apagar

        //@ open pre();

        int c = seq.getCounter(0);
        // @ open [_]System_out(?s);
        System.out.printf("Counter 0 with value: %d\n", c);
        seq.remCounter(0);
        System.out.printf("Removed counter 0\n");

        //@ close pos();
            
        
    }
}