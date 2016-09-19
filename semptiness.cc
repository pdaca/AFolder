/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <sstream>
#include <cassert>
#include <utility>
#include <iomanip>
#include "automata.h"
#include "semptiness.h"
#include "parikh.h"
#include "graph.h"

using std::vector;
using std::set;
using std::deque;
using std::map;
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

  static inline state_t toStateId(state_t s, uint mode, uint nmax){
    return s*nmax + mode;
  }
    
  static inline state_t toStateRev(state_t s, uint nmax){
    return s/nmax;
  }
    
  static inline uint toModeRev(state_t s,  uint nmax){
    return s%nmax;
  }


  // Create mode variables
  static void createModeVars(context& c, uint k, uint nmax, string postfix,
			     vector<vector<expr>>& reg,
			     vector<vector<expr>>& rev,
			     vector<vector<expr>>& arr,
			     vector<vector<expr>>& startc,
			     vector<vector<expr>>& endc){
    
    for (uint i=0; i<k; i++){
      for (uint j=0; j<nmax; j++){
	string reg_name = "reg_" + to_string(i) +"_"+to_string(j)+postfix;
	reg.at(i).at(j) = c.int_const(reg_name.c_str());
	string rev_name = "rev_" + to_string(i) +"_"+to_string(j)+postfix;
	rev.at(i).at(j) = c.int_const(rev_name.c_str());
	string arr_name = "arr_" + to_string(i) +"_"+to_string(j)+postfix;
	arr.at(i).at(j) = c.bool_const(arr_name.c_str());
	string sc_name = "sc_" + to_string(i) +"_"+to_string(j)+postfix;
	startc.at(i).at(j) = c.int_const(sc_name.c_str());
	string ec_name = "ec_" + to_string(i) +"_"+to_string(j)+postfix;
	endc.at(i).at(j) = c.int_const(ec_name.c_str());
      }
    }
  }



  // Add a formula, such that variable "out" contain the region id for variable "in" in the range [1,reg],
  // where reg is the region size for the for the counter
  static void addRegionFormula(context &c, solver &s,
  			       const expr &in,
  			       const expr& out,
  			       const set<uint>& const_set){
    int m = const_set.size();
    if (m == 0) {
      s.add(out == 1);
      return;
    }

    int r = 0;
    auto it=const_set.begin();
    counter_t prev = *it;
    if (prev > 0){
      r++;
      s.add(implies(in < prev, out == r));
    }
    r++;
    s.add(implies(in == prev, out == r));
    it++;

    for(; it!=const_set.end(); it++){
      counter_t curr = *it;
      r++;
      s.add(implies(in == curr, out == r));
      if (curr > prev + 1){
  	r++;
  	s.add(implies((prev < in)  && (in < curr), out == r));
      }
      prev = curr;
    }

    r++;
    s.add(implies(in > prev, out == r));
  }


  static void addRegionFormula(context &c, solver &s,
			       const vector<expr>& scons,
  			       const expr &in,
  			       const expr& out,
  			       const set<uint>& cons,
			       const set<uint>& symids,
			       bool cmp_symid_simple){
    assert(cons.empty() || symids.empty());

    if (!cons.empty()){
      addRegionFormula(c, s, in, out, cons);
    } else {
      
      if (symids.empty()){
	s.add(out == 1);
	return;
      }
      
      auto it=symids.begin();
      expr prev = scons.at(*it);
      s.add(implies(in < prev, out == 1));
      if (cmp_symid_simple)
	s.add(implies(in >= prev, out == 2));
      else
	s.add(implies(in == prev, out == 2));
      it++;

      int r = 3;
      for(; it!=symids.end(); it++){
	const expr& curr = scons.at(*it);
	s.add(implies((prev < in) && (in < curr), out == r));
	r++;
	s.add(implies(in == curr, out == r ));
	r++;
	prev = curr;
      }

      if (!cmp_symid_simple)
	s.add(implies(in > prev, out == r));
    }
  }


  // Add init formula.
  static void addInitFormula(solver& s, uint k, 
  			     const vector<set<uint>>& cmp_constants,
			     const vector<set<uint>>& cmp_symid,
  			     const vector<vector<expr>>& reg,
  			     const vector<vector<expr>>& rev,
  			     const vector<vector<expr>>& arr,
  			     const vector<vector<expr>>& startc,
			     const vector<expr>& scons,
			     const vector<bool> cmp_symid_simple){
    context& c = s.ctx();
    
    for (uint j=0; j<k; j++){
      const set<uint>& const_set = cmp_constants.at(j);
      const set<uint>& symid_set = cmp_symid.at(j);
      bool simple = cmp_symid_simple.at(j);
      const expr &rev_var = rev.at(j)[0];
      s.add(rev_var == 0);

      const expr &reg_var = reg.at(j)[0];
      const expr&  start_var = startc.at(j)[0];
      addRegionFormula(c, s, scons, start_var, reg_var, const_set, symid_set, simple);
    }

    // add the constraint that symbolic constants are in non-decreasing order
    for (uint i=1; i<scons.size(); i++){
      const expr& sc1 = scons.at(i-1);
      const expr& sc2 = scons.at(i);
      s.add(sc1 <= sc2);
    }
  }


  // Add the sum of elements
  void addElementSum(solver& s,
		     expr& sum_var,
		     const expr& f_var,
		     const SymbolFrm& sf){

    for (auto sc=sf.begin(); sc!=sf.end(); sc++){
      const Constant& cons = sc->cons();

      if (cons.is_symbolic()){
	cerr << "Error: it is not allow to use symbolic constansts when adding element value to a counter" << endl;
	assert(false);
      }
      
      int num = cons.num();
      
      switch (sc->op()){
      case EQ:
	s.add(sum_var = (f_var * num));
	break;
	
      case GT:
	s.add(sum_var > (f_var * num));
	break;
	  
      case LT:
	s.add(sum_var < (f_var * num));
	break;
	    
      case GEQ:
	s.add(sum_var >= (f_var * num));
	break;
	    
      case LEQ:
	s.add(sum_var <= (f_var * num));
	break;
	
      case NEQ:
	s.add(sum_var != (f_var * num));
	break;

      default:
	assert(false);
      }      
    }
  }


  // Add the sum of updates to counters by the given action.
  template <typename T>
  static void addSumFromAction(solver& s,
			       const SCM<T>& cm,
			       const map<pair<state_t, NfaAction>, expr>& flow_map,
			       map<pair<uint, pair<state_t, NfaAction>>, expr>& sum_map,
			       const map<pair<state_t, NfaAction>,pair<state_t, CmAction>>& action_map,
			       vector<vector<expr>>& sum_same,
			       vector<vector<expr>>& sum_next,
			       const NfaAction& na,
			       state_t p_mode,
			       uint p,
			       uint nmax,
			       string postfix){
        context& c = s.ctx();
        uint k  = cm.counters_no();

	uint q = na.succ();
	state_t q_mode = toModeRev(q, nmax);
	assert(p_mode == q_mode || (p_mode + 1) == q_mode);

	pair<state_t, NfaAction> ppr {p, na};
	auto elem = action_map.find(ppr);
	assert(elem != action_map.end());
	
	const pair<state_t, CmAction>& spr = elem->second;
	const CmAction& cam = spr.second;

	auto elem_f = flow_map.find(ppr);
	const expr& f_var = elem_f -> second;
	
    	const vector<int>& add = cam.addition();
	const vector<bool>& add_elem = cam.add_element();

	for (uint j=0; j<k; j++){
	  expr& sum = p_mode == q_mode ? sum_same.at(j).at(p_mode) : sum_next.at(j).at(p_mode);
	  int u = add.at(j);
	  
	  if (add_elem.at(j)){
	      // add the element value
	      uint letter_id = cam.letter_id();
	      const vector<T>& alphabet = cm.alphabet();
	      const T& letter = alphabet.at(letter_id);

	      pair<uint, pair<state_t, NfaAction> > cppr {j, ppr};
	      string sum_name = "sum_"+to_string(p)
		+"_"+to_string(na.letter_id())+"_"+to_string(q)+"_"+to_string(j)+postfix;
	      expr sum_var = c.int_const(sum_name.c_str());
	      sum_map.insert(make_pair(cppr, sum_var));
		
	      addElementSum(s, sum_var, f_var, letter);
	      sum = sum + sum_var;
	    } else if (u != 0) {
	      // add a constant
	      sum = sum + (u * f_var);
	    }
	}
  }


  template <typename T>
  static void addRespectFormula(solver& s, uint nmax,
				const SCM<T>& cm,
				const NFA<CmAction>& nfa,
  				const vector<set<uint>> cmp_constants,
  				const vector<set<uint>> cmp_symid,
  				const vector<vector<expr>>& reg,
  				const vector<vector<expr>>& rev,
  				const vector<vector<expr>>& arr,
  				const vector<vector<expr>>& startc,
  				const vector<vector<expr>>& endc,
  			        const vector<expr>& aparikh,
  				const vector<expr>& scons,
				const map<pair<state_t, NfaAction>, expr>& flow_map,
				map<pair<uint, pair<state_t, NfaAction>>, expr>& sum_map,
				const map<pair<state_t, NfaAction>,pair<state_t, CmAction>>& action_map,
				const vector<bool> cmp_symid_simple,
				string postfix){

    context& c = s.ctx();
    uint states_no = nfa.states_no();
    uint k  = cm.counters_no();
    const vector<deque<NfaAction>>& tr = nfa.tr();
    //const vector<deque<CmAction>>& tr_cm = cm.tr();
    
    // incr.at(i).at(j) is the list of incrementing updates for counter i in mode j
    vector<vector<deque<expr>>> incr (k, vector<deque<expr>>(nmax)); 
    vector<vector<deque<expr>>> decr (k, vector<deque<expr>>(nmax));
    
    for (uint p=0; p<states_no; p++){
      const deque<NfaAction>& trans = tr.at(p);
      
      for (auto it=trans.begin(); it!=trans.end(); it++){
	const NfaAction& na = *it;
	
	pair<state_t, NfaAction> ppr {p, na};
	auto elem = action_map.find(ppr);
	assert(elem != action_map.end());
	
	const pair<state_t, CmAction>& spr = elem->second;
	const CmAction& cam = spr.second;
	const vector<int>& add = cam.addition();
        
	for (uint i=0; i<k; i++){
	  int u = add.at(i);
	  
	  if (u == 0)
	    continue;
	  
	  auto elem_f = flow_map.find(ppr);
	  assert(elem_f != flow_map.end());
	  const expr& f_var = elem_f->second;
	  uint j = toModeRev(p, nmax);
	  
	  if (u>0){
	    incr.at(i)
	      .at(j)
	      .push_back(f_var);
	  }
	  else if (u<0){
	  decr.at(i)
	    .at(j)
	    .push_back(f_var);
	  }
	}      	
      }
    }
  
    // when non-incrementing (non-decrementing) allow only certain updates
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax; i++){
    	const expr& arr_var = arr.at(j).at(i);

  	const deque<expr>& incr_deq = incr.at(j).at(i);
  	if (!incr_deq.empty()){
  	  expr inf = c.bool_val(true);
		
  	  for (auto it = incr_deq.begin(); it!=incr_deq.end(); it++){
	    const expr& fvar = *it;
  	    inf = inf && (fvar == 0);
  	  }
  	  s.add(implies(arr_var, inf));
  	}

  	const deque<expr>& decr_deq = decr.at(j).at(i);
  	if (!decr_deq.empty()){
  	  expr def = c.bool_val(true);
		
  	  for (auto it = decr_deq.begin(); it!=decr_deq.end(); it++){
	    const expr& fvar = *it;
  	    def = def && (fvar == 0);
  	  }
  	  s.add(implies(!arr_var, def));
  	}
      }
    }

    expr zero = c.int_val(0);
    // sum_same.at(i).at(j) is the total additon to counter i in mode j
    vector<vector<expr>> sum_same (k, vector<expr>(nmax, zero));
    // sum_same.at(i).at(j) is the total additon to counter i when moving
    // from mode j to j+1
    vector<vector<expr>> sum_next (k, vector<expr>(nmax-1, zero));
    
    // constraints for the start and end counter values in each mode
    for (uint p=0; p<states_no; p++){
      uint p_mode = toModeRev(p, nmax);
	  
      const deque<NfaAction>& trans = tr.at(p);

      for (auto it=trans.begin(); it!=trans.end(); it++){
	const NfaAction& na = *it;

	// pair<state_t, NfaAction> ppr {p, na};
	// auto elem = action_map.find(ppr);
	// assert(elem != action_map.end());
	
	// const pair<state_t, CmAction>& spr = elem->second;
	// const CmAction& cam = spr.second;

	// auto elem_f = flow_map.find(ppr);
	// const expr& f_var = elem_f -> second;

	// does the transiton add the same mode, or to the next one?

	//expr& sum = p_mode == q_mode ? sum_same.at(j).at(p_mode) : sum_next.at(j).at(p_mode);
	addSumFromAction(s,cm,flow_map,sum_map,action_map,sum_same,sum_next,na,p_mode,p,nmax,postfix);	
      }
    }

    for (uint i=0; i<k; i++){
      for (uint j=0; j<nmax; j++){
	const expr& sum_same_var = sum_same.at(i).at(j);
	const expr& start_var = startc.at(i).at(j);
	const expr& end_var = endc.at(i).at(j);
	s.add(end_var == start_var + sum_same_var);
	
	if (j==nmax-1)
	  continue;
	
	const expr& sum_next_var = sum_next.at(i).at(j);
	const expr& start_next_var = startc.at(i).at(j+1);
	s.add(start_next_var ==  end_var + sum_next_var);
      }
    }

    // constraints that related start and end counter values to their regions	
    for (uint j=0; j<k; j++){
      const set<uint>& const_set = cmp_constants.at(j);
      const set<uint>& symid_set = cmp_symid.at(j);
      bool simple = cmp_symid_simple.at(j);
      
      for (uint i=0; i<nmax; i++){
  	const expr& reg_var = reg.at(j).at(i);
  	const expr& start_var = startc.at(j).at(i);
  	const expr& end_var = endc.at(j).at(i);
	addRegionFormula(c, s, scons, start_var, reg_var, const_set, symid_set, simple);
  	addRegionFormula(c, s, scons, end_var, reg_var, const_set, symid_set, simple);	  
      }
    }

    // constraint that start counters satisfy executed counter tests
    for (uint p=0; p<states_no; p++){
      const deque<NfaAction>& trans = tr.at(p);
      uint i = toModeRev(p, nmax);

      for (auto it=trans.begin(); it!=trans.end(); it++){
	const NfaAction& na = *it;

	pair<state_t, NfaAction> ppr {p, na};
	auto elem = action_map.find(ppr);
	assert(elem != action_map.end());
	
	const pair<state_t, CmAction>& spr = elem->second;
	const CmAction& cam = spr.second;
	const set<SCounterConstraint> ccs = cam.counter_constraints();

	  	// build a formula for the counter constraint
  	for (auto itc=ccs.begin(); itc!=ccs.end(); itc++){
  	  const SCounterConstraint& cc = *itc;
  	  uint ctr_id = cc.ctr_id();
  	  Constant cons = cc.cons();
  	  const expr& start_var = startc[ctr_id].at(i);
	  
	  auto elem_f = flow_map.find(ppr);
	  assert(elem_f != flow_map.end());
  	  const expr& f_var = elem_f->second;
	  
  	  expr val_var = cons.is_symbolic() ? scons.at(cons.sym_id()) : c.int_val(cons.num());
	  
  	  switch (cc.op()){
  	  case EQ:
  	    s.add(implies(f_var > 0, start_var == val_var)); 
  	    break;
	
  	  case GT:
  	    s.add(implies(f_var > 0, start_var > val_var)); 
  	    break;

  	  case LT:
  	    s.add(implies(f_var > 0, start_var < val_var)); 
  	    break;

  	  case GEQ:
  	    s.add(implies(f_var > 0, start_var >= val_var)); 
  	    break;

  	  case LEQ:
  	    s.add(implies(f_var > 0 , start_var <= val_var)); 
  	    break;

	  case NEQ:
  	    s.add(implies(f_var > 0 , start_var != val_var)); 
  	    break;
  	  };
  	}
      }
    }

    // require counters and the start and end of modes to be non-zero
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax; i++){
  	const expr &start_var = startc.at(j).at(i);
  	const expr &end_var = endc.at(j).at(i);
  	s.add(start_var >= 0);
  	s.add(end_var >= 0);
      }
    }    
  }


  static  void  addGoodSeqFormula(solver &s,
  				  uint k, uint nmax,
  				  uint r,
  				  const vector<set<uint>>& cmp_constants,
  				  const vector<set<uint>>& cmp_symids,
  				  const vector<vector<expr>>& reg,
  				  const vector<vector<expr>>& rev,
  				  const vector<vector<expr>>& arr){
    
    // constraint rev.at(j).at(i) to the range [0, r] and reg.at(i).at(j) is in
    // the range [1, reg_no], where reg_no is the number of regions
    // for the counter
    
    for (uint j=0; j<k; j++){
      set<uint> const_set = cmp_constants.at(j);
      // TODO reg formula not precise, and probably not even usefull
      // int reg_no = const_set.size()>0 ? 2*const_set.size() : 1;
      
      for (uint i=0; i<nmax; i++){
  	const expr &rev_var = rev.at(j).at(i);
  	s.add(rev_var >= 0);
  	s.add(rev_var <= ((int) r));
  	// const expr &reg_var = reg.at(j).at(i);
  	// s.add(1 <= reg_var);
  	// s.add(reg_var <= reg_no);
      }
    }
    
    // change in direction increase the number of reversals
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax-1; i++){
  	const expr &rev_var = rev.at(j).at(i);
  	const expr &rev_next_var = rev.at(j).at(i+1);
  	const expr &arr_var = arr.at(j).at(i);
  	const expr &arr_next_var = arr.at(j).at(i+1);
  	s.add(implies(arr_var != arr_next_var, rev_next_var == (rev_var + 1 )));
  	s.add(implies(arr_var == arr_next_var, rev_next_var == rev_var));
      }
    }

    // relate arr to the changes in reg
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax-1; i++){
  	const expr &reg_var = reg.at(j).at(i);
  	const expr &reg_next_var = reg.at(j).at(i+1);
  	const expr &arr_next_var = arr.at(j).at(i+1);
  	s.add(implies(reg_var < reg_next_var, !arr_next_var));
  	s.add(implies(reg_var > reg_next_var, arr_next_var));
      }
    }
  }

  
  // // Counts regions for numeric constants.
  static uint regionsNo(const set<uint>& cons){
    uint r = cons.size();
    if (r == 0)
      return 1;
    
    auto it=cons.begin();
    uint prev = *it;
    if (prev > 0)
      r++;	
    it++;
      
    for(; it!=cons.end(); it++){
      uint curr = *it;
      if (curr > prev + 1)
  	r++;
      prev = curr;
    }
    return r+1;
  }


  // Add constraint that b_svar <-> sf is sat
  static void addSymbolFormulaConstraint(solver& s,
					 const SymbolFrm& sf,
					 const vector<expr>& scons,
					 const expr& b_svar,
					 const expr& svar,
					 const string& postfix){

    context& c = s.ctx();
    expr sat = c.bool_val(true);
	  
    for (auto it=sf.begin(); it!=sf.end(); it++){
      const SymbolConstraint& sc = *it;
      const Constant& cons = sc.cons();

      expr val_var = cons.is_symbolic() ? scons.at(cons.sym_id()) : c.int_val(cons.num());

      switch (sc.op()){
  	  case EQ:
	    sat = sat && (svar == val_var);
  	    break;
	
  	  case GT:
	    sat = sat && (svar > val_var);
  	    break;

  	  case LT:
	    sat = sat && (svar < val_var);
  	    break;

  	  case GEQ:
	    sat = sat && (svar >= val_var);
  	    break;

  	  case LEQ:
	    sat = sat && (svar <= val_var);
  	    break;

      case NEQ:
	sat = sat && (svar != val_var);
	break;
      };
    }

    if (sf.empty()){
      sat = sat && (svar > 0);	// no constraint take any value 
    }

    s.add(b_svar == sat);
  }
  
  static void addSymbolFormula(solver& s,
			       const SCM<SymbolFrm>& cm,
			       const string& postfix,
			       const vector<expr>& scons,
			       const vector<expr>& svars,
			       const map<pair<state_t, NfaAction>, expr>& flow_map,
			       const map<pair<state_t, NfaAction>,pair<state_t, CmAction>>& action_map){

    context& c = s.ctx();
    const vector<SymbolFrm>& alphabet = cm.alphabet();
    uint alphabet_no = cm.alphabet().size();
    vector<expr> bool_svars; // bool variables that represent sat of symbol constraints

    for (uint i=0; i<alphabet_no; i++){
      const SymbolFrm& sf = alphabet.at(i);
      string name = "sb_" + to_string(i) + "_" + postfix;
      const expr b_svar = c.bool_const(name.c_str());
      const expr& s_var = svars.at(i);
      bool_svars.push_back(b_svar);
      addSymbolFormulaConstraint(s, sf, scons, b_svar, s_var,  postfix);
    }
    
    for (auto it=flow_map.begin(); it!=flow_map.end(); it++){
	  const pair<state_t, NfaAction>& ppr = it->first;
	  const expr& f_var = it->second;
	  
	  auto elem=action_map.find(ppr);
	  const pair<state_t, CmAction>& spr = elem->second;
	  uint letter_id = spr.second.letter_id();
	  const expr& s_var = bool_svars[letter_id];
	  s.add(implies((f_var > 0), s_var)); 	// if positive flow, then symbol formula is sat
    }
  }


  // TODO be more precise
  static uint regionsNo(const set<uint>& cons,
  			const set<uint>& symids,
			bool symid_simple){
    assert(cons.empty() || symids.empty());

    if (!cons.empty()){
      return regionsNo(cons);
    } else {
      if (symid_simple)
	return 2;	// constraints are complementary
      else
	return 2*symids.size() + 1;
    }
  }

				// 


  template<>
  void SCMEmptinessCheck<SymbolFrm>::addEmptinessFormula(solver& s, 
					      uint r,
					      string postfix){
    context& c = s.ctx();

    uint scons_no = cm_.sym_constants_no();
    SCMInfo info = getSCMInfo<SymbolFrm>(cm_);
    
    const vector<set<uint>>& cmp_const = info.cmp_const_;
    const vector<set<uint>>& cmp_symid = info.cmp_symid_;
    const vector<bool>& cmp_symid_simple = info.cmp_symid_simple_;
    const set<set<SCounterConstraint>>& cons_set = info.cmp_set_;

    // Assume that each counter uses either numeric or symbolic
    // comparisons, and that all symbolic values are sorted. TODO:
    // relax this
    for (uint j=0; j<k_; j++){
      assert(cmp_const.at(j).empty() || cmp_symid.at(j).empty());
    }

    uint movesno = 0;		// number of move changes per reversal
    vector<uint> moves (k_);
    for (uint i=0; i<k_; i++){
      moves.at(i) = regionsNo(cmp_const.at(i), cmp_symid.at(i), cmp_symid_simple.at(i));
      movesno += moves.at(i)-1;
    }

    nmax_ = 1+movesno*(r+1);

#ifdef INFO
    cout << "Check CM emptiness" << endl
	 << "k="<< k_ << ", r=" << r << ", moves per counter=" << moves
	 << ", nmax=" << nmax_ << ", tr_size= " << info.tr_size_ << endl;
    cout << "cmp constants: " << endl;
    for (uint j=0; j<k_; j++){
      cout << "c_" << j << " = " << cmp_const.at(j) << endl;
    }
    cout << "cmp symids: " << endl;
    for (uint j=0; j<k_; j++){
      cout << "c_" << j << " = " << cmp_symid.at(j) << endl;
    }
    cout << "guards:" ;
    for (auto it=cons_set.begin(); it!=cons_set.end(); it++){
      const set<SCounterConstraint>& ccs = *it;
      cout << "[";
      for (auto itc=ccs.begin(); itc!=ccs.end(); itc++){
	cout << *itc << ",";
      }
      cout << "]" << endl;
    }
#endif

    // create mode variables
    expr ff =  c.bool_val(false);
    reg_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff)); // reg_.at(j).at(i) is reg_j^i
    rev_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff));
    arr_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff));
    startc_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff));
    endc_ = vector<vector<expr>>(k_,vector<expr>(nmax_, ff));
    createModeVars(c, k_, nmax_, postfix, reg_, rev_, arr_, startc_, endc_);

    // create symbolic constants
    scons_ = vector<expr> (scons_no, ff);
    for (uint i=0; i<scons_no; i++){
      string sname = "sym_" + to_string(i) + postfix;
      scons_.at(i) = c.int_const(sname.c_str());
    }

    // create variables for symbol letters
    uint alphabet_no = cm_.alphabet().size();
    
    svars_ = vector<expr> (alphabet_no, ff);
    for (uint i=0; i<alphabet_no; i++){
      string name = "sv_" + to_string(i) + "_" + postfix;
      svars_.at(i) = c.int_const(name.c_str());
      //      addSymbolFormulaConstraint(s, sf, scons_, s_var, i, postfix);
    }

    //create NFA
    nfa_ = toNFA(cm_, nmax_, action_map_);
    uint alpha_nfa_no = nfa_.alphabet_no();

    // create parikh variables
    expr zero = c.int_val(0);
    aparikh_ = vector<expr> (alpha_nfa_no, zero);
    for (uint i=0; i<alpha_nfa_no; i++){
      string name = "a_" + to_string(i) + postfix;
      aparikh_.at(i) = c.int_const(name.c_str());
    }

    addParikhFormula(s, nfa_, aparikh_, postfix, flow_map_);
    addInitFormula(s, k_, cmp_const, cmp_symid, reg_, rev_, arr_, startc_, scons_, cmp_symid_simple);
    addGoodSeqFormula(s, k_, nmax_, r, cmp_const, cmp_symid, reg_, rev_, arr_);
    addRespectFormula(s, nmax_, cm_, nfa_, cmp_const, cmp_symid, reg_, rev_, arr_,
    		      startc_, endc_, aparikh_, scons_, flow_map_, sum_map_, action_map_,
		      cmp_symid_simple, postfix);
    addSymbolFormula(s, cm_, postfix, scons_, svars_, flow_map_, action_map_);
  }



  

  template <typename T>
    NFA<CmAction> SCMEmptinessCheck<T>::toNFA(const SCM<T>& cm,
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
	  tr[p_nfa].push_back(na);

	  pair<state_t, NfaAction> ppr{p_nfa, na};
	  action_map.insert(make_pair(ppr, spr));

	  if (i == nmax - 1)
	    continue;

	  // transition to the next mode
	  state_t q_nfa2 = toStateId(q, i+1, nmax);
	  NfaAction na2 {next_free, q_nfa2};
	  tr[p_nfa].push_back(na2);

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


  static void printVars(const model &model, std::ostream& os,
			uint k, uint nmax, uint WIDTH,
		       const vector<vector<expr>> vars, 
		       string name ){

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



  // Construct a weighted graph from the NFA and the model.  The
  // graph consists of the NFA states, and the weighted of edges is
  // taken from the model.
  static WeightedLabeledGraph<uint> constructGraph(const model& model,
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



  vector<pair<state_t,NfaAction>> nfaWordFromModel(const model& model,
						   const NFA<CmAction>& nfa,
						   uint nmax,
						   const map<pair<state_t, NfaAction>, expr>& flow_map,
						   const map<pair<state_t, NfaAction>,pair<state_t, CmAction>>& action_map) {
    WeightedLabeledGraph<uint> graph = constructGraph(model, nfa, nmax,
						   flow_map, action_map);

    const vector<deque<NfaAction>>& tr = nfa.tr();
    uint start = nfa.init_state();
    const map<pair<uint, uint>, uint>& label = graph.label_;

#ifdef DEBUG
    cout << "Graph" << endl;
    cout << graph << endl;
#endif
    deque<uint> epath = getEulerianPath(graph, start);

#ifdef DEBUG    
    cout << "Eulerian path" << endl;
    cout << epath << endl << endl;
#endif

    int states_no = nfa.states_no();
    vector<pair<state_t,NfaAction> > word;    

    int p = -1;
    for (auto it=epath.begin(); it!=epath.end(); it++){
      uint q = *it;
      
      if ((p!=-1) && (p<states_no)){
	// find the nfa transition
		pair<uint, uint> pr {p,q};
	auto elem = label.find(pr);
	
	const NfaAction& na = tr.at(p).at(elem->second);
	pair<state_t, NfaAction> pair{p,na};
	word.push_back(pair);
      }
      p = q;
    }    
    return word;
  }
  

  template <typename T>
  vector<CmAction> SCMEmptinessCheck<T>::wordFromModel(const model& model) {
    vector<pair<state_t,NfaAction>> nfa_word = nfaWordFromModel(model, nfa_, nmax_,
								flow_map_, action_map_);
    vector<CmAction> word{};
    
    for (auto it=nfa_word.begin(); it!=nfa_word.end(); it++){
      const pair<state_t,NfaAction>& pr = *it;
      auto elem = action_map_.find(pr);
      const pair<state_t,CmAction>& pr2 = elem->second;
      word.push_back(pr2.second);

    }
    return word;
  }



  template <>
  vector<int> SCMEmptinessCheck<SymbolFrm>::ewordFromModel(const model& m1) {
    vector<pair<state_t,NfaAction>> nfa_word = nfaWordFromModel(m1, nfa_, nmax_,
								flow_map_, action_map_);

    uint k = cm_.counters_no();
    const vector<SymbolFrm>& alphabet = cm_.alphabet();

#ifdef DEBUG
    cout << "NFA word" << endl;
    for (auto it=nfa_word.begin(); it!=nfa_word.end(); it++){
      state_t p = it->first;
      cout << it->second << ", mode=" <<  toModeRev(p,nmax_) << endl;
    }
    cout << endl;
#endif

    // build a ILP that gives values for actions
    context c2;
    solver s2(c2);
    expr tt =  c2.bool_val(true);
    expr zero = c2.int_val(0);


    vector<expr> symbol_vars(nfa_word.size(), tt);	// symbol value
    for (uint i=0; i<nfa_word.size(); i++){
      string name = "a_" + to_string(i);
      symbol_vars.at(i) = c2.int_const(name.c_str());
    }

    vector<expr> scons2(scons_.size(),zero);			// get copy of scons
    for (uint i=0; i<scons_.size(); i++){
      int val =  getZ3IntValue(m1, scons_.at(i));      	
      scons2.at(i) = c2.int_val(val);
    }

    vector<expr> cnt_vars(k, zero);			// current counter values
    
    state_t prev_mode = 0;
    if (nfa_word.size() > 0){
      state_t p = nfa_word[0].first;
      prev_mode = toModeRev(p,nmax_);
    }
    
    
    for (uint i=0; i<nfa_word.size(); i++){
      const pair<state_t,NfaAction>& pr= nfa_word[i];
      state_t p = pr.first;
      const NfaAction& na = pr.second;
      state_t q = na.succ();
      state_t mode = toModeRev(q,nmax_);
      
      pair<state_t, NfaAction> pr2 {p, na};
      auto elem = action_map_.find(pr2);
      const CmAction& cma = elem->second.second;
      const vector<int>& addition = cma.addition();
      const vector<bool>& add_element = cma.add_element();
      const SymbolFrm& sf = alphabet[cma.letter_id()];      

      addSymbolFormulaConstraint(s2, sf, scons2, tt, symbol_vars[i], "");
      bool new_mode = (mode != prev_mode);
      
      if (new_mode){
	// the mode changes, so add constrains (counter_value = "value at the end of the previous mode")
	// set counter values to the value at the end of the previous mode
	for (uint j=0; j<k; j++){
	  const expr& end_var = endc_.at(j).at(prev_mode);
	  uint endval =  getZ3UintValue(m1, end_var);      	

	  expr& cnt_var = cnt_vars.at(j);
	  s2.add(cnt_var == ((int) endval));
	  cnt_vars.at(j) = c2.int_val(endval);
	}
      }

      // update counter values by the action
      for (uint j=0; j<k; j++){
	expr& cnt_var = cnt_vars.at(j);
	if (add_element.at(j)){
	  cnt_var = cnt_var + symbol_vars.at(i);
	}
	else if (addition.at(j) != 0){
	  cnt_var = cnt_var + addition.at(j);
	}
      }

      if (new_mode){
	// add contraint (counter_value = "value at the begining of the new mode"
	// set counter value to the value at the begginng of the new mode
	for (uint j=0; j<k; j++){
	  const expr& start_var = startc_.at(j).at(mode);
	  uint startval = getZ3UintValue(m1, start_var);
	  expr& cnt_var = cnt_vars.at(j);	  
	  s2.add(cnt_var == ((int) startval));
	  cnt_vars.at(j) = c2.int_val(startval);
	}
      }
      prev_mode = mode;
    }

    // add final values
    for (uint j=0; j<k; j++){
      const expr& end_var = endc_.at(j).at(prev_mode);
      uint endval =  getZ3UintValue(m1, end_var);      	
      
      expr& cnt_var = cnt_vars.at(j);
      s2.add(cnt_var == ((int) endval));
    }


#ifdef DEBUG
    cout << "Model formula" << endl;
    cout << s2 << endl;
#endif

    
    bool sat = s2.check();
    assert(sat);
    model m2 = s2.get_model();

    // get concrete values
    vector<int> eword (nfa_word.size());
    
    for (uint i=0; i<nfa_word.size(); i++){
      const expr& var = symbol_vars.at(i);
      int val = getZ3IntValue(m2, var);
      eword[i] = val;
    }
            
    return eword;
  }
  

  template <typename T>
  void SCMEmptinessCheck<T>::printModel(const model& model, std::ostream& os){
    const uint WIDTH = 10;

    printVars(model, os, k_, nmax_, WIDTH, startc_, "start");
    os << endl;
    printVars(model, os, k_, nmax_, WIDTH, endc_, "end");
    os << endl;
    printVars(model, os, k_, nmax_, WIDTH, reg_, "reg");
    os << endl;
    printVars(model, os, k_, nmax_, WIDTH, rev_, "rev");
    os << endl;
    printVars(model, os, k_, nmax_, WIDTH, arr_, "arr");
    os << endl;

#if 0
    const vector<string>& alphabet_symbols = nfa_.alphabet_symbols();
    os << "Parikh image" << endl;    
    for (uint i=0; i<aparikh_.size(); i++){
      const expr& var = aparikh_.at(i);
      os << alphabet_symbols.at(i) << " = " << model.eval(var) << endl;
    }
#endif
  }

    template class SCMEmptinessCheck<SymbolFrm>;

}



