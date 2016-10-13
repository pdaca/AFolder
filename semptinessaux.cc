/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <sstream>
#include <cassert>
#include <utility>
#include <iomanip>
#include "automata.h"
#include "parikh.h"

#include "semptinessaux.h"

using std::vector;
using std::set;
using std::deque;
using std::map;
using std::list;
using std::to_string;
using std::cout;
using std::cerr;
using std::endl;
using std::flush;
using std::move;
using std::pair;
using std::make_pair;
using std::setw;
using std::string;
using namespace z3;

namespace fold {

  std::ostream& operator<<(std::ostream& os,
				  const Region& reg){
    if (!reg.l_incl_ || reg.l_isinf_)
      os << "(";
    else
      os << "[";

    if (reg.l_isinf_)
      os << "-∞";
    else
      os << reg.l_cnst_;

    os << ",";

    if (reg.u_isinf_)
      os << "+∞";
    else
      os << reg.u_cnst_;
    
    if (!reg.u_incl_ || reg.u_isinf_)
      os << ")";
    else
      os << "]";

    return os;
  }


  std::ostream& operator<<(std::ostream& os, const std::list<Region>& regs){
    for (auto it=regs.begin(); it!=regs.end(); it++)
      os << *it << ", ";

    return os;
  }




  // Compute regions when there no symbolic constants
  static void regionsNoNumeric(uint i,
			       const SCMInfo& info,
			       list<Region>& regs){
    set<SCounterConstraint> ccs = info.ccs_vector_.at(i);
    set<pair<Constant, Operator>, ConstOperatorCmp> ccops {};

    for (auto it=ccs.begin(); it!=ccs.end(); it++){
      const SCounterConstraint& cc = *it;
      assert(cc.ctr_id() == i);
      const Constant& cons = cc.cons();
      Operator op = cc.op();
      ccops.insert(make_pair(cons, op));
    }

    //  the lower bound for the next region
    bool l_inf = true;
    int l_val = 0;
    Constant l_cnst {false, l_val, 0};
    bool l_incl = false;
    
    for (auto it=ccops.begin(); it!=ccops.end(); it++){      
      int val = it->first.num();
      assert (!it->first.is_symbolic());
      Operator op = it->second;

      switch (op){
      case EQ:
      case NEQ:{
	// |l_cnst; cons-1] and [cons; cons]
	if (l_inf || (l_val <= val-1)){
	  Constant cons {false, val-1, 0};
	  Region reg1 {l_cnst, l_incl, l_inf, cons, true, false};
	  regs.push_back(reg1);
	}
	// [const; cons]
	Constant cons {false, val, 0};
	Region reg2 {cons, true, false , cons, true, false};
	regs.push_back(reg2);
	l_val = val+1;
	l_cnst = Constant{false, l_val, 0};
	l_inf = false;
	l_incl =true;
	break;
      }

      case LT:
      case GEQ:{
	// |l_cnst; cons-1]
	if (l_inf || (l_val <= val-1)){
	  Constant cons {false, val-1, 0};
	  Region reg1 {l_cnst, l_incl, l_inf, cons, true, false};
	  regs.push_back(reg1);
	  l_val = val;
	  l_cnst = Constant{false, l_val, 0};
	  l_inf = false;
	  l_incl =true;
	}
	break;
      }

      case GT:
      case LEQ:{
	// |l_cnst; cons]
	if (l_inf || (l_val <= val)){
	  Constant cons {false, val, 0};
	  Region reg1 {l_cnst, l_incl, l_inf, cons, true, false};
	  regs.push_back(reg1);
	  l_val = val+1;
	  l_cnst = Constant{false, l_val, 0};
	  l_inf = false;
	  l_incl =true;
	}
	break;
      }

      default:
	assert(false);
      }
    }

    // |l_cnst; +infinity)
    Region reg {l_cnst, l_incl, l_inf, l_cnst, false, true};
    regs.push_back(reg);   
  }

  // Compute regions when there are symbolic constants
  static void regionsNoSymbolic(uint i,
				const vector<expr>& scons_srt_ctr,
				const SCMInfo& info,
				list<Region>& regs){
    set<SCounterConstraint> ccs = info.ccs_vector_.at(i);    
    set<pair<Constant, Operator>, ConstOperatorCmp> ccops {};

    // we don't the ordering between numeric and unsorted constants,
    // so create regions for the cross product of operatos and sorted
    // symbolic constants
    set<Operator> ops;    
    
    for (auto it=ccs.begin(); it!=ccs.end(); it++){
      const SCounterConstraint& cc = *it;
      assert(cc.ctr_id() == i);
      Operator op = cc.op();
      ops.insert(op);
    }

    for (uint j=0; j<scons_srt_ctr.size(); j++){
      Constant cons {true, 0, j};

      for (auto it=ops.begin(); it!=ops.end(); it++){
	ccops.insert(make_pair(cons, *it));	
      }      
    }

    //  the lower bound for the next region
    bool l_inf = true;
    Constant l_cnst {false, 0, 0};
    bool l_incl = false;
    
    for (auto it=ccops.begin(); it!=ccops.end(); it++){
      const Constant& cons = it->first;
      Operator op = it->second;

      switch (op){
      case EQ:
      case NEQ:{
	// |l_cnst; cons) and [cons; cons]
	if (l_inf || (l_cnst != cons)){
	    Region reg1 {l_cnst, l_incl, l_inf, cons, false, false};
	    regs.push_back(reg1);
	}
	// [const; cons]
	Region reg2 {cons, true, false , cons, true, false};
	regs.push_back(reg2);
	l_cnst = cons;
	l_inf = false;
	l_incl = false;
	break;
      }

      case LT:
      case GEQ:{
	// |l_cnst; cons)
	if (l_inf || (l_cnst != cons)){
	    Region reg1 {l_cnst, l_incl, l_inf, cons, false, false};
	    regs.push_back(reg1);
	    l_cnst = cons;
	    l_inf = false;
	    l_incl = true;	
	  }
	break;
      }

      case GT:
      case LEQ:{
	// |l_cnst; cons]
	if (l_inf || l_incl || (l_cnst != cons)){
	  Region reg1 {l_cnst, l_incl, l_inf, cons, true, false};
	  regs.push_back(reg1);
	  l_cnst = cons;
	  l_inf = false;
	  l_incl = false;
	}
	break;
      }

      default:
	assert(false);
      }
    }

    // |l_cnst; +infinity)
    Region reg {l_cnst, l_incl, l_inf, l_cnst, false, true};
    regs.push_back(reg);
  }

  
  void regionsNo(uint i,
		 const vector<expr>& scons_srt_ctr,
		 const SCMInfo& info,
		 list<Region>& regs){
    if (info.cmp_symid_.at(i).empty()){
      regionsNoNumeric(i, info, regs);
    } else {
      regionsNoSymbolic(i, scons_srt_ctr, info, regs);
    }
  }



  void printVars(const model &model, std::ostream& os,
			uint k, uint nmax, uint WIDTH,
		       const vector<vector<expr>>& vars, 
		       string name){

    os << std::left << setw(WIDTH) << name << "|";
    
    for (uint i=0; i<nmax; i++){
      os << setw(WIDTH) << ("m"+to_string(i)) << "|";
    }
    os << endl;

    for (uint j=0; j<k; j++){
      os << setw(WIDTH) << ("c"+to_string(j)) << "|";
      for (uint i=0; i<nmax; i++){
	const expr& var = vars.at(j).at(i);
	os << setw(WIDTH) << model.eval(var) << "|";
      }
      os << endl;
    }
  }


  WeightedLabeledGraph<uint> constructGraph(const model& model,
						   const NFA<CmAction>& nfa,
						   uint nmax,
						   const map<pair<state_t, NfaAction>, expr>& flow_map,
						   const map<pair<state_t, NfaAction>,pair<state_t, CmAction>>& action_map){

    // map transition of NFA to new states;

    uint states_no = nfa.states_no() + action_map.size()+1;
    uint next_free = nfa.states_no();
    map<pair<uint,uint>, uint> weight;
    map<pair<uint,uint>, uint> labels;

    // doesnt matter
    vector<uint> alphabet{};
    
    const vector<deque<NfaAction>>& tr = nfa.tr();
    
    for (uint p=0; p<nfa.states_no(); p++){
      const deque<NfaAction>& trans = tr.at(p);

      uint i=0;
      for (auto it=trans.begin(); it!=trans.end(); it++){
	const NfaAction& na = *it;

	state_t q = na.succ();

	pair<state_t, NfaAction> ppr {p, na};
	auto elem_f = flow_map.find(ppr);
	const expr& flow_var = elem_f->second;
	uint flow = getZ3UintValue(model, flow_var);

	// adds intermediate state;
	uint w = next_free++;

	weight[make_pair(p,w)] = flow;
	weight[make_pair(w,q)] = flow;
	// labels saves the number of the NFA transition from state p
	labels[make_pair(p,w)] = i;
	i++;
      }
    }
    
    WeightedLabeledGraph<uint> graph(states_no, weight, labels, alphabet);

    return move(graph);
  }



  
  

  template <typename T>
  NFA<CmAction> toNFA(const SCM<T>& cm,
		      uint nmax,
		      map<pair<state_t, NfaAction>,pair<state_t, CmAction>>& action_map){
    
    uint states_no_cm = cm.states_no();
    const vector<deque<CmAction>>& tr_cm = cm.tr();
    const set<state_t>& acc_cm = cm.accepting();
    state_t init_cm = cm.init_state();
	  
    uint states_no = nmax * states_no_cm;

    // construct accepting and init
    state_t init = toStateId(init_cm, 0, nmax);
    set<state_t> acc;
    for (auto it=acc_cm.begin(); it!=acc_cm.end(); it++){
      state_t s=*it;
   
      for(uint i=0; i<nmax; i++){
	acc.insert(toStateId(s, i, nmax));
      }      
    }

    vector<CmAction> alphabet;
    // construct transition relation and fill action_map
    vector<deque<NfaAction>> tr (states_no);
    uint next_free = 0;

    for (uint p=0; p<states_no_cm; p++){
      const deque<CmAction>& trans = tr_cm.at(p);
      for (auto it=trans.begin(); it!=trans.end(); it++, next_free++){
	const CmAction& cam = *it;
	state_t q = cam.succ();

	alphabet.push_back(cam);

	pair<state_t, CmAction> spr{p, cam};

	for (uint i=0; i<nmax; i++){
	  state_t p_nfa = toStateId(p, i, nmax);

	  // transiton in the same mode
	  state_t q_nfa = toStateId(q, i, nmax);
	  NfaAction na {next_free, q_nfa};
	  tr.at(p_nfa).push_back(na);
	  pair<state_t, NfaAction> ppr{p_nfa, na};
	  action_map.insert(make_pair(ppr, spr));

	  if (i == nmax - 1)
	    continue;

	  // transition to the next mode
	  state_t q_nfa2 = toStateId(q, i+1, nmax);
	  NfaAction na2 {next_free, q_nfa2};
	  tr.at(p_nfa).push_back(na2);

	  pair<state_t, NfaAction> ppr2{p_nfa, na2};
	  action_map.insert(make_pair(ppr2, spr));
	}
      }
    }
    NFA<CmAction> control_nfa {states_no, init, alphabet, tr, acc};

#ifdef DEBUG
    cout << endl;
    cout << "NFA states no=" << states_no << endl;
    cout << control_nfa << endl;
    control_nfa.check();
#endif
    
    return move(control_nfa);
  }

  template NFA<CmAction> toNFA(const SCM<SymbolFrm>& cm,
			       uint nmax,
			       map<pair<state_t, NfaAction>,pair<state_t, CmAction>>& action_map);


}
