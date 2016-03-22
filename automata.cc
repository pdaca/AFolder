/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <set>
#include <map>
#include <cassert>

#include "automata.h"
#include "scm.h"

using std::endl;
using std::string;
using std::vector;
using std::deque;
using std::set;
using std::map;
using std::move;

namespace fold {

  std::ostream& operator<<(std::ostream& os,
			     const NfaAction& na){
    return os << "letter=" << na.letter_id_ 
	      << ",succ=" << na.succ_;       
  }

  template <typename T>
  const vector<deque<NfaAction>>& NFA<T>::tr_rev() {
    if (tr_rev_.empty() && states_no_ > 0){
      vector<deque<NfaAction>> tr_rev (states_no_);

      for (uint s=0; s<states_no_; s++){
	const deque<NfaAction>& trans = tr_[s];
	for (auto it=trans.begin(); it!=trans.end(); it++){
	  const NfaAction& na = *it;
	  NfaAction rev{na.letter_id(), s};
	  tr_rev[na.succ()].push_back(rev);
	}
      }
      tr_rev_ = std::move(tr_rev);
    }

    return tr_rev_;
  }


  template <typename T>
  void NFA<T>::check() {
    if (tr_.size() != states_no_)
	assert(false);
    
      if (init_state() >=  states_no_)
	assert(false);

      for (uint s=0; s<states_no_; s++){
	const std::deque<NfaAction>& trans = tr_[s];
      	for (auto it=trans.begin(); it!=trans.end(); it++){
	  const NfaAction& na = *it;

	  if (na.succ() >= states_no_){
	    assert(false);
	  }

	  if (na.letter_id() >= alphabet_.size()){
	    assert(false);
	  }	  
	}
      }
    }

    template <typename U>
    std::ostream& operator<<(std::ostream& os,
			     const NFA<U>& nfa){
    os << "NFA : states_no=" << nfa.states_no()
       << ", init_state=" << nfa.init_state() 
       << ", accepting=" << nfa.accepting()
       << ", alphabet=" << std::endl;
    uint i=0;
    for (auto it=nfa.alphabet().begin(); it!=nfa.alphabet().end(); it++, i++){
      os << i << "->" << *it << std::endl;
    }

    for (uint st = 0; st < nfa.states_no_; st++){
      const std::deque<NfaAction>& d = nfa.tr_[st];
      for (auto it=d.begin(); it!=d.end(); it++){
	os << "s=" << st << "," << *it << std::endl;
      }
    }

    return os;
  }

  template std::ostream& operator<<(std::ostream& os,
				    const NFA<SymbolFrm>& nfa);

  template std::ostream& operator<<(std::ostream& os,
				    const NFA<CmAction>& nfa);


  template class  NFA<SymbolFrm>;
  template class  NFA<CmAction>;






//   // minimize a DFA.
//   NFA minimize(NFA& nfa, vector<state_t>& state2eq){
//     uint states_no = nfa.states_no();
//     const vector<string>& alphabet = nfa.alphabet_symbols();
//     const set<state_t>& accepting = nfa.accepting();
//     const vector<vector<vector<state_t>>>& tr = nfa.tr();
//     const vector<vector<set<state_t>>>& tr_rev = nfa.tr_rev();

//     // (p,q) pair encoded as p*states_no + q;
//     deque<ullong> new_marked;
//     set<ullong> marked;
    
//     for (auto ita=accepting.begin(); ita!=accepting.end(); ita++){
//       state_t p = *ita;

//       for(uint q=0; q<states_no; q++){
// 	auto fnd = accepting.find(q);
// 	if (fnd == accepting.end()){
// 	  ullong pr = p*states_no + q;
// 	  new_marked.push_back(pr);
// 	}
//       }	
//     }

//     while (!new_marked.empty()){
//       ullong pr = new_marked.front();
//       new_marked.pop_front();

//       if (marked.find(pr) == marked.end())
// 	marked.insert(pr);
//       else
// 	continue;
//       state_t p = pr / states_no;
//       state_t q = pr % states_no;

//       for (uint a=0; a<alphabet.size(); a++){
// 	const set<state_t>& bp = tr_rev[p][a];
// 	const set<state_t>& bq = tr_rev[q][a];

// 	for (auto itp=bp.begin(); itp!=bp.end(); itp++){
// 	  state_t p2 = *itp;
// 	  for (auto itq=bq.begin(); itq!=bq.end(); itq++){
// 	    state_t q2 = *itq;
// 	    ullong pr2 = p2 * states_no + q2;
// 	    new_marked.push_back(pr2);	    
// 	  }
// 	}
//       }
//     }

//     state_t nextfree = 0;
//     vector<state_t> eq2repr; 
    
//     for (uint p=0; p<states_no; p++){
//       bool found = false;
      
//       for (uint q=0; q<states_no; q++){
// 	ullong pr = p*states_no + q;
	
// 	if (marked.find(pr) == marked.end()){
// 	  // q is the representative
// 	  if (p == q){
// 	    // create new eq class
// 	    state2eq[p] = nextfree;
// 	    nextfree++;
// 	    eq2repr.push_back(p);
// 	  } else {
// 	    state2eq[p] = state2eq[q];
// 	  }
// 	  found = true;
// 	  break;
// 	}
//       }
//       assert(found);
//     }

//     uint sn_min = nextfree;
//     state_t init_min = state2eq[nfa.init_state()];
    
//     set<state_t> acc_min;
//     for (auto ita=accepting.begin(); ita!=accepting.end(); ita++){
//       state_t q = state2eq[*ita];
//       acc_min.insert(q);
//     }

// #ifdef DEBUG
// #endif

//     vector<vector<vector<state_t> > > tr_min (sn_min, vector<vector<state_t> > (alphabet.size()));

//     for (uint e=0; e<sn_min; e++){
//       state_t r = eq2repr[e];
//       for (uint a=0; a<alphabet.size(); a++){
// 	const vector<state_t>& succ=tr[r][a];
// 	assert(succ.size() <= 1);
// 	if (succ.empty())
// 	  continue;

// 	state_t esucc = state2eq[succ[0]];
// 	tr_min[e][a].push_back(esucc);
//       }
//     }
    
//     NFA nfa_min{sn_min, init_min, alphabet, tr_min, acc_min};
// #ifdef DEBUG
//     assert(nfa_min.check());
// #endif
//     return nfa_min;  
//   }

  
}
