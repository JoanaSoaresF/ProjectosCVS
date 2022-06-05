/**
 * CVS 2021-22 Project- Task 2
 * Authors
 * Gonçalo Martins Lourenço nº55780
 * Joana Soares Faria nº55754
 */

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
predicate_ctor CCSeq_shared_state (CCSeq s) () = s.seq |-> ?cs &*& cs != null
                                    &*& CounterSequenceInv(cs, _, _);
@*/

/*@ predicate CCSeqInv(CCSeq s;) = s.monitor |-> ?lock
                             &*& lock != null 
                             &*& lck(lock, 1, CCSeq_shared_state(s))
                             &*& s.notFull |-> ?nf_con
                             &*& nf_con != null
                             &*& cond(nf_con, CCSeq_shared_state(s), CCSeq_notfull(s))
                             &*& s.notEmpty |-> ?ne_con
                             &*& ne_con != null
                             &*& cond(ne_con, CCSeq_shared_state(s), CCSeq_notempty(s))
                             ;
@*/

/*@ 
predicate_ctor CCSeq_notfull (CCSeq s) () = s.seq |-> ?cs 
                                    &*& cs.capacity |-> ?c 
                                    &*& cs.nCounters |-> ?n 
                                    &*& n >= 0 &*& n < c;

predicate_ctor CCSeq_notempty (CCSeq s) () = s.seq |-> ?cs 
                                    &*& cs.capacity |-> ?c 
                                    &*& cs.nCounters |-> ?n 
                                    &*& n > 0 &*& n <= c;
@*/

public class CCSeq {

    CounterSequence seq;
    ReentrantLock monitor;
    Condition notFull; 
    Condition notEmpty;

    public CCSeq(int cap) 
    //@ requires cap > 0;
    //@ ensures CCSeqInv(this);
    {
        // TODO
        seq = new CounterSequence(cap);
        //@ close CCSeq_shared_state(this)(); 
        //@ close enter_lck(1,CCSeq_shared_state(this));
        monitor = new ReentrantLock();
        //@ close set_cond(CCSeq_shared_state(this),CCSeq_notfull(this));
        notFull = monitor.newCondition();
        //@ close set_cond(CCSeq_shared_state(this),CCSeq_notempty(this));
        notEmpty = monitor.newCondition();
        //@ close CCSeqInv(this);
    }

    public int getCounter(int i) 
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        // TODO
        int result = -1;
        //@ open [f]CCSeqInv(this);
        monitor.lock();
        //@ open CCSeq_shared_state(this)();
        if(i >= 0  && i < seq.length()) {
            //valid index
            result = seq.getCounter(i);
        } 
        //@ close CCSeq_shared_state(this)();
        monitor.unlock();
        return result;
    }

    public void incr(int i, int val) 
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        // TODO
        //@ open [f]CCSeqInv(this);
        monitor.lock();
        //@ open CCSeq_shared_state(this)();
        if(i >= 0 && i<seq.length() && val >= 0) {
            //valid index
            seq.increment(i, val);
        } 
        //@ close CCSeq_shared_state(this)();
        monitor.unlock();
        
    }

    public void decr(int i, int val) 
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        // TODO
         //@ open [f]CCSeqInv(this);
         monitor.lock();
         //@ open CCSeq_shared_state(this)();
         if(i >= 0 && i<seq.length() && val >= 0) {
             //valid index
             seq.decrement(i, val);
         } 
         //@ close CCSeq_shared_state(this)();
         monitor.unlock();
    }

    public int addCounter(int limit) 
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        // TODO
         //@ open [f]CCSeqInv(this);
         monitor.lock();
         //@ open CCSeq_shared_state(this)();
         if(seq.length()== seq.capacity()) {
             // @ close CCSeq_shared_state(this)();
             try {
                notFull.await();
            } catch (InterruptedException e) {
            }
            //FIXME No matching heap chunks: CounterSequence_sequence(cs0, _)
             //@ open CCSeq_notfull(this)();
         } 
    
         int n = seq.length();
         seq.addCounter(limit);
         //@ close CCSeq_notempty(this)();
         notEmpty.signal();
         //@ close CCSeq_shared_state(this)();
         monitor.unlock();
         //@ close [f]CCSeqInv(this);
        return n;
    }

    public void remCounter(int i) 
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        // TODO
            //@ open [f]CCSeqInv(this);
            monitor.lock();
            //@ open CCSeq_shared_state(this)();

            if(i >= 0 && i<seq.capacity()) {
                //valid index
                if(seq.length()== 0) {
                    //@ close CCSeq_shared_state(this)();
                    try {
                        notEmpty.await();
                    } catch (InterruptedException e) {
                    }
                    //@ open CCSeq_notempty(this)();
                } 
                //FIXME No matching heap chunks: CounterSequence_sequence(cs0, _)
                seq.remCounter(i);
                //@ close CCSeq_notfull(this)();
                notFull.signal();
            } 
            //@ close CCSeq_shared_state(this)();
            monitor.unlock();
            //@ close [f]CCSeqInv(this);
    }

}
