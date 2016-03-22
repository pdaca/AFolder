/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <utility>
#include "parikh.h"
#include "scm.h"

using std::vector;
using std::map;
using std::set;
using std::deque;
using std::string;
using std::to_string;
using std::pair;
using std::make_pair;
using namespace z3;

namespace fold {

  // Add flow constraints as in "Counting in Tree for Free."
  template <typename T>
  static void addFlowConstraints(solver& s,
				 const map<pair<state_t, NfaAction>, expr>& flow_map,
				 NFA<T> &nfa,
				 string postfix){
    context& c = s.ctx();
    uint states_no = nfa.states_no();
    const vector<deque<NfaAction>>& tr = nfa.tr();
    const vector<deque<NfaAction>>& tr_rev = nfa.tr_rev();
    const set<state_t>& acc = nfa.accepting();
    state_t init_state = nfa.init_state();
    expr acc_sum = c.int_val("0");
 
    for (state_t p=0; p< states_no; p++){
      expr in = c.int_val("0");
      expr out = c.int_val("0");

      const deque<NfaAction>& trans = tr.at(p);
      
      for (auto it=trans.begin(); it!=trans.end(); it++){
	const NfaAction& na = *it;
	auto elem = flow_map.find(make_pair(p, na));
	assert(elem != flow_map.end());
	const expr& v = elem->second;
	out = out + v;
	s.add(v >= 0);
      }

      const deque<NfaAction>& trans_rev = tr_rev.at(p);

      for (auto it=trans_rev.begin(); it!=trans_rev.end(); it++){
	const NfaAction& na = *it;
	NfaAction rev {na.letter_id(), p};
	auto elem = flow_map.find(make_pair(na.succ(), rev));
	assert(elem != flow_map.end());
	const expr& v = elem->second;
	in = in + v;
	//	s.add(v >= 0);
      }
      
      if (p == init_state){
	out = out - c.int_val(1);
      }
      
      if (acc.find(p) != acc.end()){
	string name = "z_"+to_string(p) + postfix;
	expr z = c.int_const(name.c_str());
	acc_sum = acc_sum + z;
	out = out + z;
	s.add(z >= 0);
      }
      s.add(in == out);
    }
    
    s.add(acc_sum == 1);
  }
  
  
  // Add reach constraints as in "Counting in Tree for Free."
  template <typename T>
  static void addReachConstraints(solver& s,
				  const map<pair<state_t, NfaAction>, expr>& flow_map,
				  const map<uint, expr>& reach_map,
				  NFA<T> &nfa){
    context& c = s.ctx();
    uint states_no = nfa.states_no();
    const vector<deque<NfaAction>>& tr_rev = nfa.tr_rev();
    state_t init_state = nfa.init_state();

    for (uint p=0; p<states_no; p++){
      auto r_elem = reach_map.find(p);
      assert(r_elem != reach_map.end());
      
      const expr& r_var = r_elem->second;

      if ( init_state ==  p){
	s.add(r_var == 0);
	continue;
      }
      s.add(r_var > 0);

      expr reach_cond = c.bool_val(false);
      expr not_connected = c.bool_val(true);

      const deque<NfaAction>& trans_rev = tr_rev.at(p);
      for (auto it=trans_rev.begin(); it!=trans_rev.end(); it++){
	const NfaAction& na_rev = *it;
	state_t q = na_rev.succ();
	NfaAction na{na_rev.letter_id(), p};
	auto elem = flow_map.find(make_pair(q, na));
	assert (elem != flow_map.end());
	const expr& tr_var = elem->second;

	auto predp = reach_map.find(q);
	assert (predp != reach_map.end());

	const expr& r_pred = predp->second;	  
	expr disj = ((r_var > r_pred) && (tr_var > 0));
	reach_cond = reach_cond || disj;
	not_connected = not_connected && (tr_var == 0);
      }

      s.add(reach_cond || not_connected);
    }
  }
  


  // Add multiplicity constraints for symbols in the alphabet.
  template <typename T>
  static void addAlphabetConstraints(solver& s,
				     const map<pair<state_t, NfaAction>, expr>& flow_map,
				     const vector<expr>& aparikh,
				     const NFA<T> &nfa){
    context& c = s.ctx();
    uint states_no = nfa.states_no();
    uint alphabet_no = nfa.alphabet_no();
    const vector<deque<NfaAction>>& tr = nfa.tr();

    map<uint, expr> sum_map;
    for (symbol_t a=0; a<alphabet_no; a++){
      expr var = c.int_val(0);
      sum_map.insert(make_pair(a,var));
    }
    
    for (state_t p=0; p< states_no; p++){
      const deque<NfaAction>& trans = tr.at(p);
      
      for (auto it=trans.begin(); it!=trans.end(); it++){
	const NfaAction& na = *it;
	uint a = na.letter_id();

	auto a_elem = sum_map.find(a);
	assert (a_elem != sum_map.end());
	expr& a_var = a_elem->second;

	auto elem = flow_map.find(make_pair(p, na));
	assert (elem != flow_map.end());
	const expr& tr_var = elem->second;
	a_var = a_var + tr_var;	
      }
    }
    for (symbol_t a=0; a<alphabet_no; a++){
      const expr& a_var = aparikh.at(a);
      auto sum_elem = sum_map.find(a);
      assert (sum_elem != sum_map.end());
      expr& sum_var = sum_elem->second;
      s.add(a_var == sum_var);
    }
  }
  
  template <typename T>
  void addParikhFormula(solver &s,
			NFA<T>& nfa,
			const vector<expr>& aparikh,
			string postfix,
			map<pair<state_t, NfaAction>, expr>& flow_map){
    assert(aparikh.size() == nfa.alphabet_no());

    context& c = s.ctx();
    uint states_no = nfa.states_no();
    const vector<deque<NfaAction>>& tr = nfa.tr();

    // create variables
    map<uint, expr> reach_map;

    for (uint p=0; p< states_no; p++){
      string name = "r_"+to_string(p)+postfix;
      expr var = c.int_const(name.c_str());
      reach_map.insert(make_pair(p, var));
      
      const deque<NfaAction>& trans = tr.at(p);
      
      for (auto it=trans.begin(); it!=trans.end(); it++){
	const NfaAction& na = *it;
	state_t q = na.succ();
	string namep = "x_"+to_string(p)
	  +"_"+to_string(na.letter_id())+"_"+to_string(q)+postfix;
	expr varp = c.int_const(namep.c_str());
	pair<state_t, NfaAction> pr{p, na};
	flow_map.insert(make_pair(pr, varp));
      }
    }

    addFlowConstraints(s, flow_map, nfa, postfix);
    addReachConstraints(s, flow_map, reach_map, nfa);
    addAlphabetConstraints(s, flow_map, aparikh, nfa);
  }


  template void addFlowConstraints(solver& s,
				   const map<pair<state_t, NfaAction>, expr>& flow_map,
				   NFA<CmAction> &nfa,
				   string postfix);
  
  template void addReachConstraints(solver& s,
				    const map<pair<state_t, NfaAction>, expr>& flow_map,
				    const map<uint, expr>& reach_map,
				    NFA<CmAction> &nfa);
  
  template void addAlphabetConstraints(solver& s,
				     const map<pair<state_t, NfaAction>, expr>& flow_map,
				     const vector<expr>& aparikh,
				       const NFA<CmAction> &nfa);
  
  template void addParikhFormula(solver &s,
				 NFA<CmAction>& nfa,
				 const vector<expr>& aparikh,
				 string postfix,
				 map<pair<state_t, NfaAction>, expr>& flow_map);

}
