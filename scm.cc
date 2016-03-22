/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/ 
#include <map>
#include <cassert>
#include "scm.h"
#include "z3++.h"

using std::endl;
using std::string;
using std::vector;
using std::map;
using std::deque;
using std::set;
using std::move;
using std::pair;
using std::make_pair;
using namespace z3;

namespace fold {

  bool Constant::operator<(const Constant& o) const {
    if (this == &o){
      return false;
    }
    
    if (!is_symbolic_ && o.is_symbolic_){
      return true;
    }

    if (is_symbolic_ && !o.is_symbolic_){
      return false;
    }

    if (is_symbolic_ && sym_id_ < o.sym_id_){
      return true;
    }

    if (!is_symbolic_ && num_ < o.num_){
      return true;
    }

    return false;
  }
  

  std::ostream& operator<<(std::ostream& os, const Constant& cons){
    if (cons.is_symbolic_){
      return os << "s" + std::to_string(cons.sym_id_);
    } else {
      return os << std::to_string(cons.num_);
    }
  }


  bool SCounterConstraint::operator<(const SCounterConstraint& o) const{
    if (this == &o){
      return false;
    }
      
    if (ctr_id_ < o.ctr_id_){
      return true;
    }

    if (ctr_id_ > o.ctr_id_){
      return false;
    }

    if (op_ < o.op_){
      return true;
    }

    if (op_ > o.op_){
      return false;
    }

    if (cons_ < o.cons_){
      return true;
    }

    return false;
  }


  std::ostream& operator<<(std::ostream& os, const SCounterConstraint& cc) {
    os << "c_" << cc.ctr_id();

    switch (cc.op_){
    case EQ :
      os << "=";
      break;

    case GT :
      os << ">";
      break;

    case LT :
      os << "<";
      break;

    case GEQ :
      os << ">=";
      break;

    case LEQ :
      os << "<=";
      break;

    case NEQ :
      os << "!=";
      break;

    default :
      os << "?";
    }

    return os << cc.cons_;
  }


  std::ostream& operator<<(std::ostream& os, const std::set<SCounterConstraint>& ccs){
    os << "[";
    for (auto it=ccs.begin(); it!=ccs.end(); it++){
      os << *it << ",";
    }
    return os << "]";
  }


  bool SymbolConstraint::operator<(const SymbolConstraint& o) const{
    if (this == &o){
      return false;
    }
    if (op_ < o.op_){
      return true;
    }
    
    if (op_ > o.op_){
      return false;
    }
    
    if (cons_ < o.cons_){
      return true;
    }

    return false;
  }


  std::ostream& operator<<(std::ostream& os, const SymbolConstraint& sc){
    os << "inp";

    switch (sc.op_){
    case EQ :
      os << "=";
      break;

    case GT :
      os << ">";
      break;

    case LT :
      os << "<";
      break;

    case GEQ :
      os << ">=";
      break;

    case LEQ :
      os << "<=";
      break;

    case NEQ :
      os << "!=";
      break;


    default :
      os << "?";
    }

    return os << sc.cons_;
  }


  std::ostream& operator<<(std::ostream& os, const SymbolFrm& sf){
    os << "[";
    for (auto it=sf.begin(); it!=sf.end(); it++){
      os << *it << ",";
    }
    return os << "]";
  }
  

  std::ostream& operator<<(std::ostream& os, const CmAction& cma){
    return os << "letter=" << cma.letter_id_ << "," <<cma.ccs_
	      << ",succ=" << cma.succ_
	      << ",add=" << cma.addition_;
  }


  template <typename T>
  void SCM<T>::check() const {
    if (tr_.size() != states_no_)
      assert(false);

    if (init_state() >=  states_no_)
      assert(false);

    for (uint st=0; st<states_no_; st++){
      const deque<CmAction>& d = tr_[st];

      for (auto itd=d.begin(); itd!=d.end(); itd++){
	const CmAction& cma = *itd;

	if (cma.letter_id() >= alphabet_.size())
	  assert(false);
      
	state_t succ = cma.succ();

	if (succ >= states_no_)
	  assert(false);

	const set<SCounterConstraint>& scc = cma.counter_constraints();
	for (auto it=scc.begin(); it!=scc.end(); it++){
	  const SCounterConstraint& cc = *it;
	  if (cc.ctr_id() >= counters_no_)
	    assert(false);

	  const Constant& cs = cc.cons();
	  if (cs.is_symbolic() && cs.sym_id() >= sym_constants_no()){
	    assert(false);
	  }
	}      
      }
    }
  }

  
  template void SCM<SymbolFrm>::check() const;

  
  template <typename U>
  std::ostream& operator<<(std::ostream& os,
			   const SCM<U>& cm){
    os << "SCM : states_no=" << cm.states_no()
       << ", counters_no=" << cm.counters_no()
       << ", symb. consts=" << cm.sym_constants_no()
       << ", init_state=" << cm.init_state() 
       << ", accepting=" << cm.accepting()
       << ", alphabet=" << std::endl;
    uint i=0;
    for (auto it=cm.alphabet().begin(); it!=cm.alphabet().end(); it++, i++){
      os << i << "->" << *it << std::endl;
    }

    for (uint st = 0; st < cm.states_no_; st++){
      const std::deque<CmAction>& d = cm.tr_[st];
      for (auto it=d.begin(); it!=d.end(); it++){
	os << "s=" << st << "," << *it << std::endl;
      }
    }

    return os;
  }


  template   std::ostream& operator<<(std::ostream& os,
				      const SCM<SymbolFrm>& cm);


  static bool checkSfSat(const SymbolFrm& sf, uint scons_no){
    context c2;
    solver s2(c2);

    vector<expr> scons;
    for(uint i=0; i<scons_no; i++){
      string name = "SCT" + std::to_string(i);
      expr scon = c2.int_const(name.c_str());
      scons.push_back(scon);
    }

    expr svar = c2.int_const("SCT");
    expr sat = c2.bool_val(true);
	 
    for (auto it=sf.begin(); it!=sf.end(); it++){
      const SymbolConstraint& sc = *it;
      const Constant& cons = sc.cons();

      expr val_var = cons.is_symbolic() ? scons.at(cons.sym_id()) : c2.int_val(cons.num());

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

    s2.add(sat);
    return s2.check();
  }
  

  SCM<SymbolFrm> parallel(const SCM<SymbolFrm>& cm1,
			  const SCM<SymbolFrm>& cm2){
    uint counters_no1 = cm1.counters_no();
    state_t init_state1 = cm1.init_state();
    uint scons1 = cm1.sym_constants_no();
    const vector<SymbolFrm>& alpha1 = cm1.alphabet();
    const vector<deque<CmAction>>& tr_1 = cm1.tr();
    const set<state_t>& acc1 = cm1.accepting();

    uint states_no2 = cm2.states_no();
    uint counters_no2 = cm2.counters_no();
    uint scons2 = cm2.sym_constants_no();
    const vector<SymbolFrm>& alpha2 = cm2.alphabet();
    state_t init_state2 = cm2.init_state();
    const vector<deque<CmAction>>& tr_2 = cm2.tr();
    const set<state_t>& acc2 = cm2.accepting();

    // map from symbol formula to (sat, combined letter id)
    map<SymbolFrm, pair<bool, uint>> alphabet_map;

    // maps a pair c to a state in the parallel composition, such that
    // s1 = c/(size of cm2), s2 = c%(size of cm2).
    map<ullong, state_t> state_map; 
    uint counters_no = counters_no1 + counters_no2;
    uint scons = scons1 + scons2;
    state_t init_state = 0;
    ullong init_pair = init_state1*states_no2 + init_state2;
    state_map[init_pair] = init_state;
    
    // construct tr and accepting
    vector<deque<CmAction>> tr;
    set<state_t> acc;
    
    deque<ullong> worklist {};
    set<ullong> done {};
    worklist.push_back(init_pair);
    state_t next_free = 1;
    while(!worklist.empty()){
      ullong ps = worklist.front();
      worklist.pop_front();

      if (done.find(ps) == done.end())
	done.insert(ps);
      else
	continue;

      auto elem_s = state_map.find(ps);
      assert(elem_s != state_map.end());
      state_t s = elem_s->second;
      uint s1 = ps/states_no2;
      uint s2 = ps%states_no2;
      
      if (acc1.find(s1) != acc1.end() && acc2.find(s2) != acc2.end())
	acc.insert(s);

      const deque<CmAction>& acts1 = tr_1[s1];
      const deque<CmAction>& acts2 = tr_2[s2];

      for (auto it1=acts1.begin(); it1!=acts1.end(); it1++){
	const CmAction& cam1 = *it1;
	uint letter_id1 = cam1.letter_id();
	const SymbolFrm& sf1 = alpha1[letter_id1];
	const set<SCounterConstraint>& ccs1 = cam1.counter_constraints();
	uint succ1 = cam1.succ();
	const vector<int>& add1 = cam1.addition();
	
	for (auto it2=acts2.begin(); it2!=acts2.end(); it2++){
	  const CmAction& cam2 = *it2;

	  uint letter_id2 = cam2.letter_id();
	  const SymbolFrm& sf2 = alpha2[letter_id2];

	  SymbolFrm sf {sf1};
	  
	  for (auto it_sf=sf2.begin(); it_sf!=sf2.end(); it_sf++){
	    const SymbolConstraint& old_sc = *it_sf;
	    const Constant& old_const = old_sc.cons();

	    Constant new_const {old_const.is_symbolic()
		, old_const.num()
		, old_const.sym_id() + scons1};

	    SymbolConstraint new_sc {old_sc.op(), new_const};
	    sf.insert(new_sc);
	  }
	  
	  auto elem_a = alphabet_map.find(sf);
	  pair<bool, uint> res;
	  if (elem_a == alphabet_map.end()){
	    //TODO do some pre-sat check
	    bool sat = checkSfSat(sf, scons);
	    //	    bool sat = true;
#ifdef DEBUG
	    if (!sat) {
	      std::cout << "SF " << sf << " is unsat" << std::endl;
	    }
#endif
	      
	    res = make_pair(sat, alphabet_map.size());
	    alphabet_map.insert(make_pair(sf, res));
	  }
	  else {
	    res = elem_a->second;
	  }

	  if (!res.first){
	    continue;
	  }
	  uint letter_id = res.second;
	  
	  const set<SCounterConstraint>& ccs2 = cam2.counter_constraints();
	  uint succ2 = cam2.succ();
	  const vector<int>& add2 = cam2.addition();

	  // TODO replace vector with deques
	  set<SCounterConstraint> ccs;

	  for (auto it=ccs1.begin(); it!=ccs1.end(); it++){
	    ccs.insert(*it);
	  }

	  for (auto it=ccs2.begin(); it!=ccs2.end(); it++){
	    const SCounterConstraint& old_nsc = *it;
	    const Constant& old_c = old_nsc.cons();
	    Constant new_c {old_c.is_symbolic(), old_c.num(), old_c.sym_id() + scons1};
	    SCounterConstraint nsc {counters_no1 + old_nsc.ctr_id() , old_nsc.op(), new_c};
	    ccs.insert(nsc);
	  }

	  vector<int> add (counters_no);
	  for (uint i=0; i<counters_no1; i++)
	    add[i] = add1[i];
	  
	  for (uint i=0; i<counters_no2; i++)
	    add[i+counters_no1] = add2[i];

	  // find successor id
	  ullong succ_pair = succ1 * states_no2 + succ2;
	  state_t succ;
	  auto elem = state_map.find(succ_pair);
	  if (elem == state_map.end()){
	    // successor element exists
	    succ = next_free++;
	    state_map[succ_pair] = succ;
	  } else {
	    succ = elem->second;
	  }
	  
	  CmAction cam {letter_id, ccs, succ, add};
	  if (succ >= tr.size()){
	    tr.push_back(deque<CmAction>{});
	    assert(succ <= tr.size());
	  }
	    
	  tr[s].push_back(cam);
	  worklist.push_back(succ_pair);	          
	}
      }
    }

    vector<SymbolFrm> alphabet (alphabet_map.size());
    uint i=0;
    for (auto it=alphabet_map.begin(); it!=alphabet_map.end(); it++, i++){
      uint letter_id = it->second.second;
      alphabet[letter_id] = it->first;
    }

    SCM<SymbolFrm> cm {next_free, counters_no, scons, init_state, alphabet, tr, acc};
#ifdef DEBUG
    cm.check();
#endif

    return std::move(cm);
  }


    template <typename T>
    SCMInfo getSCMInfo(const SCM<T>& scm){
    const std::vector<std::deque<CmAction>>& tr = scm.tr();
    uint counters_no = scm.counters_no();
    
    uint tr_size = 0;
    std::vector<std::set<uint>> cmp_const (counters_no);
    std::vector<std::set<uint>> cmp_symid (counters_no);
    std::vector<bool> cmp_symid_simple (counters_no);
    std::vector<uint> cmp (counters_no);
    std::set<std::set<SCounterConstraint>> cmp_set;
    std::set<std::pair<uint, int>> update_set;

    for (uint s=0; s<tr.size(); s++){
      const std::deque<CmAction>& d =  tr[s];
      tr_size += d.size();

      for (auto it=d.begin(); it!=d.end(); it++){
	const CmAction& cma = *it;

	const std::set<SCounterConstraint>& ccs = cma.counter_constraints();
	cmp_set.insert(ccs);

	for (auto itc=ccs.begin(); itc!=ccs.end(); itc++){
	  const SCounterConstraint& cc = *itc;
	  uint ctr = cc.ctr_id();
	  cmp[ctr] |= (1 << cc.op());
	  Constant cons = cc.cons();
	  if (cons.is_symbolic()){	    
	    cmp_symid[ctr].insert(cons.sym_id());
	  }
	  else {
	    cmp_const[ctr].insert(cons.num());
	  }
	}

	const std::vector<int>& add = cma.addition();
	for (uint i=0; i<counters_no; i++){
	  update_set.insert(std::make_pair(i, add[i]));
	}
      }
    }

    for (uint c=0; c<counters_no; c++){
      if ((cmp[c] == 12) && (cmp_symid[c].size() == 1)){
	cmp_symid_simple[c] = true;
      }
    }
    
    SCMInfo info {tr_size, cmp_const, cmp_symid, cmp_symid_simple, cmp_set, update_set};
    return info;
  }


  template SCMInfo getSCMInfo(const SCM<SymbolFrm>& scm);

}
