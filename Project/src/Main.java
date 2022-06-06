/**
 * CVS 2021-22 Project- Task 2
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */


public class Main {
    public static void main(String[] args) 
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true;
    {
        CCSeq seq = new CCSeq(30);
        for(int i = 0; i<100;i++)
        //@ invariant [_]CCSeqInv(seq);
        {
            new AddCounterThread(seq).run();
            // new RemoveCounterThread(seq).run();
          
            
        }

        
    }
    
}
