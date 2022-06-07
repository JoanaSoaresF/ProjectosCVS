/**
 * CVS 2021-22 Project- Task 2
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */

/*@ predicate RemoveThreadInv(RemoveCounterThread t;) = t.seq |-> ?s &*& s != null
&*& [_]CCSeqInv(s) &*& t.i |-> ?index &*& index >=0
;@*/

class RemoveCounterThread implements Runnable {

    public CCSeq seq;
    int i;
    
    /*@ predicate pre() = RemoveThreadInv(this) &*& [_]System_out(?s) &*& s != null; @*/
    //@ predicate post() = true;

    public RemoveCounterThread(CCSeq seq, int i)
    //@ requires seq != null &*& [_]CCSeqInv(seq) &*& i >=0; 
    //@ ensures RemoveThreadInv(this); 
    {
        this.seq = seq;
        this.i = i;
    }

    public void run() 
    //@ requires pre(); 
    //@ ensures post();
    {
        //@ open pre();

        int c = seq.getCounter(i);
        // @ open [_]System_out(?s);
    
        // String s = String.format("Counter %d with value: %d", i, c);
        System.out.print("Counter ");
        System.out.print(i);
        System.out.print(" with value: ");
        System.out.print(c);
        System.out.println("");

        seq.remCounter(0);
        System.out.print("Removed counter from position ");
        System.out.print(i);
        System.out.println("");
        

        //@ close post();
            
        
    }
}