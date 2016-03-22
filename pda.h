/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef PDA_H__
#define PDA_H__

#include <cassert>
#include "automata.h"


namespace fold {

  // A transition update for PDA. For simplicity we assume stack
  // operations of the form A->a, where |a|<=2.
  class PDAtransition {
  public:
  PDAtransition(state_t succ,
		uint symbol,
		const vector<uint>& update)
    : succ_ { succ}
    , symbol_ {symbol}
    , update_ {update}
    {}

    virtual ~PDAtransition()
      {};

    state_t succ_;
    uint symbol_;
    const vector<uint> update_;
    friend std::ostream& operator<<(std::ostream& os, const PDAtransition& tr);
  };
  

  // Pushdown automaton that accepts by final state.
  class PDA {
  public:
  PDA() 
    : states_no_{0}
    , init_state_{0}
    , alphabet_symbols_{}
    , stack_symbols_{}
    , tr_rel_{}
    , acc_{}
    {}
  
  PDA(unsigned int states_no, state_t init_state,
     const vector<string>& alphabet_symbols,
     const vector<string>& stack_symbols,
     const vector<vector<vector<PDAtransition>>>& tr_rel,
     const set<state_t>& acc)
    : states_no_{states_no}
    , init_state_{init_state}
    , alphabet_symbols_{alphabet_symbols}
    , stack_symbols_{stack_symbols}
    , tr_rel_{tr_rel}
    , acc_{acc}
    {}

    PDA(PDA &&other);
    PDA& operator=(PDA&& other);
      
    virtual ~PDA() 					{ }
    unsigned int states_no() const 			{ return states_no_;    }
    unsigned int alphabet_no() const			{ return alphabet_symbols_.size(); }
    const vector<string>& alphabet_symbols() const	{ return alphabet_symbols_; }
    const vector<string>& stack_symbols() const		{ return stack_symbols_; }
    state_t init_state() const				{ return init_state_; }	
    const set<state_t>& accepting() const		{ return acc_; }
    const vector<vector<vector<PDAtransition>>>& tr() const
    							{ return tr_rel_; }
    bool check();

  private:
    unsigned int states_no_;
    state_t init_state_;
    // last-beyond-alphabet symbol is epsilon 
    vector<string> alphabet_symbols_;
    // the first symbols is the start symbol
    vector<string> stack_symbols_;
    // state -> action -> successors
    vector<vector<vector<PDAtransition>>> tr_rel_;
    set<state_t> acc_;

    friend std::ostream& operator<<(std::ostream& os, const PDA& nfa);
  };    


}


#endif
