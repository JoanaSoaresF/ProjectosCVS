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
        //@ invariant [_]CCSeqInv(seq) &*& [_]System_out(?s) &*& s != null &*& i >= 0 &*& i<=100;
        {
            new Thread(new AddCounterThread(seq)).start();
            new Thread(new RemoveCounterThread(seq, 99-i)).start();
        }
    }
    
}
