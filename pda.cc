/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include "pda.h"

using std::endl;

namespace fold{

  std::ostream& operator<<(std::ostream& os, const PDAtransition& tr){
    return os << "s'"<< tr.succ_ << ",stack=" << tr.symbol_ << "->" << tr.update_;
  }

  
  PDA::PDA(PDA &&other)
    : states_no_{ other.states_no_},
      init_state_{ other.init_state_},
      alphabet_symbols_ {move(other.alphabet_symbols_)},
      stack_symbols_ {move(other.stack_symbols_)},
      tr_rel_ {move(other.tr_rel_)},
      acc_ {move(other.acc_)}
	{ }



  PDA& PDA::operator=(PDA&& other){
    states_no_ = other.states_no_;
    init_state_ = other.init_state_;
    alphabet_symbols_ = move(other.alphabet_symbols_);
    stack_symbols_ = move(other.alphabet_symbols_);
    tr_rel_ = move(other.tr_rel_);
    acc_ = move(other.acc_);
    return *this;
  }


  bool PDA::check(){
    if (alphabet_symbols_.size() == 0 || stack_symbols_.size() == 0)
      assert(false);

    if (tr_rel_.size() != states_no_)
      assert(false);

    if (init_state() >=  states_no_)
      assert(false);

    for (unsigned int st=0; st<states_no_; st++){
      const vector<vector<PDAtransition>>& va = tr_rel_[st];
      if (va.size() != alphabet_no()+1)
	assert(false);

      for (unsigned int act=0; act<alphabet_no(); act++){
	const vector<PDAtransition>& vp = va[act];

	set<state_t> s_set;
	for (unsigned int i=0; i<vp.size(); i++){
	  const PDAtransition& tr = vp[i];
	  const uint symbol = tr.symbol_;
	  const state_t succ = tr.succ_;
	  s_set.insert(succ);

	  if (succ >= states_no())
	    assert(false);

	  if (symbol >= stack_symbols_.size())
	    assert(false);
	}

	if (vp.size() != s_set.size())
	  assert(false);
      }
    }

    return true;
  }


  std::ostream& operator<<(std::ostream& os, const PDA& pda) {
    os << "PDA : states_no=" << pda.states_no()  << ", init_state=" << pda.init_state()
       << ", accepting=" << pda.accepting() << endl;
    os << "Input alphabet: " << pda.alphabet_symbols() << endl;
    os << "Stack alphabet: " << pda.stack_symbols() << endl;
    os << "Tr: " << endl;
    for (unsigned int st = 0; st < pda.states_no_; st++){
      for (unsigned int act = 0; act < pda.alphabet_no()+1; act++){
	const vector<PDAtransition>& succs = pda.tr_rel_[st][act];
	for (auto it=succs.begin(); it!=succs.end(); it++){
	os << "s=" << st;
	if (act < pda.alphabet_no())
	  os << "," << pda.alphabet_symbols()[act];
	else
	  os << "," << epsilon;
	os << ",s'=" <<  *it << endl;
	}
      }
    }

    return os;
  }

}

