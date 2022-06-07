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
    
    //@ predicate pre() = RemoveThreadInv(this) &*& [_]System_out(?s) &*& s != null;
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
        String valueString = "Counter " + String.valueOf(i) + " with value: " + String.valueOf(c);
        System.out.println(valueString);
        if(c != -1) {
            // valid counter
            seq.remCounter(0);
            String removedString = "Removed counter from position " + String.valueOf(i);
            System.out.println(removedString);
        } else {
            String invalidCounterString = "Counter " + String.valueOf(i) + " does not exist";
            System.out.println(invalidCounterString);
        }
        
        //@ close post();
            
    }
}