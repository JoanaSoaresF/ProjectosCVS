
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
                                    &*& CounterSequenceInv(cs, ?m, ?n)
                                    &*& m > 0 &*& n >= 0
                                    &*& n <= m;
@*/

//NOTE apagar?
/* @
predicate_ctor CCSeq_shared_state (CCSeq s) () = s.seq |-> ?cs &*& cs != null
                                    &*& s.N |-> ?n
                                    &*& n >= 0
                                    &*& s.MAX |-> ?m
                                    &*& m > 0
                                    &*& n <= m
                                    &*& CounterSequenceInv(cs, m, n);
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
predicate_ctor CCSeq_notfull (CCSeq s) () = s.seq |-> ?cs &*& cs != null
                                    &*& CounterSequenceInv(cs, ?c, ?n)
                                    &*& n >= 0 
                                    &*& c > 0
                                    &*& n < c;

predicate_ctor CCSeq_notempty (CCSeq s) () = s.seq |-> ?cs &*& cs != null
                                    &*& CounterSequenceInv(cs, ?m, ?n)
                                    &*& m > 0 &*& n >= 0
                                    &*& n <= m;
@*/
//NOTE apagar?
/* @
predicate_ctor CCSeq_notfull (CCSeq s) () = s.seq |-> ?cs &*& cs != null
                                    &*& s.MAX |-> ?c 
                                    &*& s.N |-> ?n 
                                    &*& n >= 0 
                                    &*& c > 0
                                    &*& n < c
                                    &*& CounterSequenceInv(cs, c, n);

predicate_ctor CCSeq_notempty (CCSeq s) () = s.seq |-> ?cs &*& cs != null
                                    &*& s.MAX |-> ?c 
                                    &*& s.N |-> ?n 
                                    &*& n > 0 
                                    &*& c > 0
                                    &*& n <= c
                                    &*& CounterSequenceInv(cs, c, n);
@*/ 

public class CCSeq {

    CounterSequence seq;
    //int N;
    //int MAX;
    ReentrantLock monitor;
    Condition notFull;
    Condition notEmpty;

    public CCSeq(int cap)
    //@ requires cap > 0;
    //@ ensures CCSeqInv(this);
    {
        //MAX = cap;
        //N = 0;
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
        int result = -1;
        //@ open [f]CCSeqInv(this);
        monitor.lock();
        //@ open [?q]CCSeq_shared_state(this)();
        if (i >= 0 && i < seq.length()) {
            // valid index
            result = seq.getCounter(i);
        }
        //@ close [q]CCSeq_shared_state(this)();
        monitor.unlock();
        return result;
    }

    public void incr(int i, int val)
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        monitor.lock();
        //@ open CCSeq_shared_state(this)();
        if (i >= 0 && i < seq.length() && val >= 0) {
            // valid index
            seq.increment(i, val);
        }
        //@ close CCSeq_shared_state(this)();
        monitor.unlock();

    }

    public void decr(int i, int val)
    //@ requires [?f]CCSeqInv(this);
    //@ ensures [f]CCSeqInv(this);
    {
        //@ open [f]CCSeqInv(this);
        monitor.lock();
        //@ open CCSeq_shared_state(this)();
        if (i >= 0 && i < seq.length() && val >= 0) {
            // valid index
            seq.decrement(i, val);
        }
        //@ close CCSeq_shared_state(this)();
        monitor.unlock();
    }

    public int addCounter(int limit)
    //@ requires [?f]CCSeqInv(this) &*& limit > 0;
    //@ ensures [f]CCSeqInv(this);
    {
        int n = -1;
        try {
            //NOTE este f pode ou nao ficar
            //@ open [f]CCSeqInv(this);
            monitor.lock();
        
            //@ open CCSeq_shared_state(this)();
            while (seq.length() == seq.capacity())
            /*@ invariant this.seq |-> ?cs &*& cs != null
            &*& CounterSequenceInv(cs,?mm,?nc)
            &*& nc>=0
            &*& mm> 0 &*& nc<=mm
            &*& [f]notFull |-> ?cc &*& cc!=null
            &*& [f]cond(cc,CCSeq_shared_state(this),CCSeq_notfull(this))
            ;@*/
            {
                //
                //
                
                //TODO fazer com o while
                //ATTENTION com while: Cannot prove dummy == mm
                
                //@ close CCSeq_shared_state(this)();

                notFull.await();
                //@ open CCSeq_notfull(this)();

            }
        
            seq.addCounter(limit);
            n = seq.length()-1;//N++;
            //@ close CCSeq_notempty(this)();
            notEmpty.signal();
        } catch (InterruptedException e) {}
    
        monitor.unlock();
        
        return n;
        //@ close [f]CCSeqInv(this);
        
    }

    public void remCounter(int i)
    //@ requires [?f]CCSeqInv(this) &*& i >= 0;
    //@ ensures [f]CCSeqInv(this);
    {      
        
        //@ open [f]CCSeqInv(this);
        monitor.lock();
        //@ open CCSeq_shared_state(this)();
        //TODO fazer ocm o while

        
        if (i < seq.length()) { 
            // @ close CCSeq_shared_state(this)();
            //monitor.unlock(); 
            //return;
        
            
            // valid index
            while (seq.length() == 0) 
                /*@ invariant this.seq |-> ?cs &*& cs != null
            &*& CounterSequenceInv(cs,?mm,?nc)
            &*& nc>=0
            &*& mm> 0 &*& nc<=mm
            &*& [f]notEmpty |-> ?cc &*& cc!=null
            &*& [f]cond(cc,CCSeq_shared_state(this),CCSeq_notempty(this))
            ;@*/
            {

                //@ close CCSeq_shared_state(this)();
                try {notEmpty.await();} catch (InterruptedException e) {}
                //@ open CCSeq_notempty(this)();

            }
            
            //12 val escolha multipla, testing, pre e pos em verifast, tratamento aliasing, fraçoes, predicados
            //precisamos de slices e slice deeps

            // @ open CCSeq_shared_state(this)();

             if (i < seq.length()) { 
                seq.remCounter(i);
                //@ close CCSeq_notfull(this)();
                notFull.signal();
            } 
        }
        
        //@ close counterSequenceInv(cs,_,_);

        //@ close CCSeq_shared_state(this)();
        //tabom, corre
        //o stor já se está a ir embora... já nao vou perguntar...
        monitor.unlock();
        //@ close [f]CCSeqInv(this);
    }

}
