/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef AUTOMATA_H__
#define AUTOMATA_H__

#include <vector>
#include <set>
#include <deque>
#include <iostream>
#include <utility>
#include <cassert>
#include "common.h"

namespace fold {

  // Transition in an NFA.
  class NfaAction {
  public:
  NfaAction(uint letter_id,
	    state_t succ)
    : letter_id_{letter_id}
    , succ_{succ}
    {}
    
    uint letter_id() const 			{ return letter_id_; }    
    state_t succ() const 			{ return succ_; }
    
    bool operator<(const NfaAction& o) const {
      if (letter_id_ < o.letter_id_){
	return true;
      }

      if (letter_id_ > o.letter_id_){
	return false;
      }

      if (succ_ < o.succ_){
	return true;
      }

      return false;
    }
    
  private:
    uint letter_id_;
    state_t succ_;
    friend std::ostream& operator<<(std::ostream& os,
				    const NfaAction& na);
  };

    
  // Non-deterministic finite automata
  template <typename T>
    class NFA{
  public:
  NFA() 
    : states_no_{0}
    , init_state_{0}
    , alphabet_{}
    , tr_{}
    , tr_rev_{}
    , acc_{}
    {}
  
  NFA(uint states_no,
      state_t init_state,
      const std::vector<T>& alphabet,
      const std::vector<std::deque<NfaAction>>& tr,      
      const std::set<state_t>& acc)
    : states_no_{states_no}
    , init_state_{init_state}
    , alphabet_{alphabet}
    , tr_{tr}
    , tr_rev_{}
    , acc_{acc}
    {}
      
    virtual ~NFA() 				 	{}
    
    uint states_no() const 				{ return states_no_;    }
    state_t init_state() const				{ return init_state_; }	
    uint alphabet_no() const				{ return alphabet_.size(); }
    const std::vector<T>& alphabet() const		{ return alphabet_; }
    const std::vector<std::deque<NfaAction>>& tr() const
    { return tr_; }
    const std::set<state_t>& accepting() const		{ return acc_; }
    const std::vector<std::deque<NfaAction>>& tr_rev();    
    void check();

  private:
    uint states_no_;
    state_t init_state_;
    std::vector<T> alphabet_;
    std::vector<std::deque<NfaAction>> tr_;
    // reverse transition relation constructed on demands
    std::vector<std::deque<NfaAction>> tr_rev_;	
    std::set<state_t> acc_;

    template <typename U>
       friend std::ostream& operator<<(std::ostream& os,
				       const NFA<U>& nfa);
  };




  
  /* // Minimize a DFA. Provides a mapping to minimized states. */
  /* NFA minimize(NFA& nfa, std::vector<state_t>& state2eq); */
}

#endif
