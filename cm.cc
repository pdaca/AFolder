/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <cassert>
#include <map>
#include "cm.h"

using std::endl;
using std::string;
using std::vector;
using std::deque;
using std::set;
using std::map;
using std::move;

namespace fold {


  CounterConstraint::CounterConstraint(uint ctr_idx,
				       Operator op,
				       counter_t val)
    : ctr_idx_ {ctr_idx}
    , op_ {op}
    , val_ { val }
      {}


  bool CounterConstraint::satisfies(vector<counter_t> v) const {
    counter_t cv = v[ctr_idx_];

    switch(op_){
    case EQ:
      return cv == val_;

    case GT:
      return cv > val_;

    case LT:
      return cv < val_;

    case GEQ:
      return cv >= val_;

    case LEQ:
      return cv <= val_;
    }

    return false;
  }


  bool CounterConstraint::operator<(const CounterConstraint& o) const{
    if (ctr_idx_ < o.ctr_idx()){
      return true;
    }

    if (ctr_idx_ == o.ctr_idx() &&  op_ < o.op()){
      return true;
    }

    if (ctr_idx_ == o.ctr_idx() &&  op_ == o.op() && val_ < o.val()){
      return true;
    }

    return false;
  }

  
  std::ostream& operator<<(std::ostream& os, const CounterConstraint& cc) {
    os << "c_" << cc.ctr_idx() ;

    switch (cc.op()){
    case EQ :
      os << "=";
      break;

    case GT :
      os << ">";
      break;

    case LT :
      os << "<";
      break;

    case LEQ :
      os << "<=";
      break;

    case GEQ :
      os << ">=";
      break;

    case NEQ :
      os << "!=";
      break;

    default :
      os << "?";
    }

    os << cc.val();
    return os;
  }



  std::ostream& operator<<(std::ostream& os, const MachineMove& mm) {
    return os << "s'=" << mm.state() << ",v=" << mm.addition();
  }


  std::ostream& operator<<(std::ostream& os, const CCSet& ccv){
    if (ccv.empty()){
      return os << "[]";
    }
    
    os << "[";
    uint i=0;
    auto it=ccv.begin();
    for (; it!=ccv.end() && i<ccv.size()-1; i++, it++)
      os << *it << ",";
    
    os << *it << "]";
    return os;
  }


  
  MachineMove& MachineMove::operator=(const MachineMove& other){
    state_ = other.state_;
    addition_ = other.addition_;
    return *this;
  }



  bool CM::check() const {
    if (tr_rel_.size() != states_no_)
      assert(false);

    if (init_state() >=  states_no_)
      assert(false);


    for (uint st=0; st<states_no_; st++){
      const vector<vector<cm_pair>> & va = tr_rel_[st];
      if (va.size() != alphabet_no())
	assert(false);

      for (uint act=0; act<alphabet_no(); act++){
	const vector<cm_pair> & vp = va[act];

	for (uint i=0; i<vp.size(); i++){
	  const cm_pair& p = vp[i];
	  const CCSet& ccv = p.first;
	  for (auto itcc=ccv.begin(); itcc!=ccv.end(); itcc++){
	    const CounterConstraint& cc = *itcc;
	    if (cc.ctr_idx() >= counters_no())
	      assert(false);	    
	  }
	  
	  const MachineMove& mm = p.second;

	  if (mm.state() >= states_no()){
	    assert(false);
	  }

	  if (mm.addition().size() != counters_no())
	    assert(false);
	}
      }
    }
    

    return true;
  }



  CM::CM(CM&& other)
    : states_no_{other.states_no_}
    , counters_no_{other.counters_no_}
    , init_state_{other.init_state_}      
    , alphabet_symbols_{move(other.alphabet_symbols_)}
    , tr_rel_{move(other.tr_rel_)}
    , acc_{move(other.acc_)}      
  {}


  CM::CM(const CM& other)
    : states_no_{other.states_no_}
    , counters_no_{other.counters_no_}
    , init_state_{other.init_state_}      
    , alphabet_symbols_{other.alphabet_symbols_}
    , tr_rel_{other.tr_rel_}
    , acc_{other.acc_}
  {}


  CM& CM::operator=(CM&& other){
    states_no_ = other.states_no_;
    counters_no_ = other.counters_no_;
    init_state_ = other.init_state_;
    alphabet_symbols_ = move(other.alphabet_symbols_);
    tr_rel_ = move(other.tr_rel_);
    acc_ = move(other.acc_);
    return *this;
  }


  CM& CM::operator=(const CM& other){
    states_no_ = other.states_no_;
    counters_no_ = other.counters_no_;
    init_state_ = other.init_state_;
    alphabet_symbols_ = other.alphabet_symbols_;
    tr_rel_ = other.tr_rel_;
    acc_ = other.acc_;
    return *this;
  }


  deque<cm_config> CM::run(const cm_config& cnf, symbol_t s) const {
    deque<cm_config> configs;

    state_t st = cnf.first;
    const vector<counter_t> counters = cnf.second;

    const vector<cm_pair>& vp = tr_rel_[st][s];
    for (auto it=vp.begin(); it!=vp.end(); it++){
      const cm_pair& cm = *it;
      const CCSet& ccv = cm.first;
      bool sat = true;
      for (auto itcc=ccv.begin(); itcc!=ccv.end(); itcc++){
	const CounterConstraint &cc = *itcc;
	if (!cc.satisfies(counters)){
	  sat = false;
	  break;
	}
      }

      const MachineMove& mm = cm.second;

      if (sat){
	vector<counter_t> new_counters = counters;
	const vector<int>& addition = mm.addition();
	for (uint i=0; i<counters_no_; i++){
	  new_counters[i] += addition[i];
	  assert(new_counters[i] >= 0);
	}

	cm_config ncnf{mm.state(), new_counters};
	configs.push_back(ncnf);
      }
    }

    return configs;
  }


  deque<cm_config> CM::run(const vector<symbol_t>& word,
			   const vector<counter_t>& init_counters) const {
    return runAll(word, init_counters).back();
  }


  deque<cm_config> CM::run(const vector<string>& word,
			   const vector<counter_t>& init_counters) const {
    return runAll(word, init_counters).back();
  }


  // TODO use sets of configs
  deque<deque<cm_config>> CM::runAll(const vector<symbol_t>& word,
				     const vector<counter_t>& init_counters) const {
    deque<deque<cm_config>> configs;
    cm_config init_config {init_state(), init_counters};
    configs.push_back(deque<cm_config>{init_config});

    for (auto it=word.begin(); it!=word.end(); it++){
      symbol_t act = *it;
      const deque<cm_config>& old_configs = configs.back();
      configs.push_back(deque<cm_config> {});
      deque<cm_config>& new_configs = configs.back();
      
      for (auto itc=old_configs.begin(); itc!=old_configs.end(); itc++){
	const cm_config& cnf = *itc;
	deque<cm_config> confs = run(cnf, act);
	for (auto itn = confs.begin(); itn != confs.end(); itn++)
	  new_configs.push_back(*itn);
      }
    }

    return configs;
  }


  deque<deque<cm_config>> CM::runAll(const vector<string>& word,
				     const vector<counter_t>& init_counters) const {

    map<string, symbol_t> s_map;
    for (uint a=0; a<alphabet_symbols_.size(); a++){
      s_map[alphabet_symbols_[a]] = a;
    }

    vector<symbol_t> nword (word.size());
    for (uint i=0; i<word.size(); i++){
      auto elem = s_map.find(word[i]);
      assert(elem != s_map.end());
      nword[i] = elem->second;
    }

    return runAll(nword, init_counters);
  }



    
  std::ostream& operator<<(std::ostream& os, const CM& cm) {
    os << "CM : states_no=" << cm.states_no()
       << ", counters_no=" << cm.counters_no()
       << ", init_state=" << cm.init_state() 
       << ", accepting=" << cm.accepting() << endl;

    for (uint st = 0; st < cm.states_no_; st++){
      for (uint act = 0; act < cm.alphabet_no(); act++){
	const vector<cm_pair> &pvector = cm.tr_rel_[st][act];
	for (uint i=0; i<pvector.size(); i++){
	  const cm_pair& pr = pvector[i];
	  os << "s=" << st;
	  os << "," << cm.alphabet_symbols()[act];
	  const CCSet& ccv = pr.first;
	  os << "," << ccv;
	  os << "," << pr.second  << endl;
	}
      }
    }

    return os;
  }


  bool CMBuilder::addMove(state_t start, state_t target, uint act,
			  const CCSet &ccv, const vector<int>& addition){
    assert(act < alphabet_symbols_.size());
    
    if (act == alphabet_symbols_.size())
      return false;
    
    if (start > (state_t) states_no_ )
      return false;
    
    vector<cm_pair>& cv = tr_rel_[start][act];
    
    MachineMove mm {target, addition};
    cv.push_back(std::make_pair(ccv, mm));
    return true;
  }


  bool CMBuilder::addMove(state_t start, state_t target, const string& action,
			  const CCSet &ccv, const vector<int>& addition){
    uint act=0;
    for (; act<alphabet_symbols_.size(); act++){
      if (alphabet_symbols_[act].compare(action) == 0)
	break;
    }

    return addMove(start, target, act, ccv, addition);
  }


  bool CMBuilder::addMove(state_t start, state_t target, const string& action,
			  const CounterConstraint& cc, const vector<int>& addition){
    return addMove(start, target, action, CCSet {cc}, addition);
  }


  bool CMBuilder::addMove(state_t start, state_t target, const string& action,
			  const vector<int>& addition){
    return addMove(start, target, action, CCSet {}, addition);
  }


  bool CMBuilder::addSelfloop(state_t state){
    vector<int> add (counters_no_, 0);
    bool sat = true;
    
    for (uint i=0; i<alphabet_symbols_.size(); i++){
      sat = sat && addMove(state, state, alphabet_symbols_[i], add);
    }
    return sat;
  }


  CM CMBuilder::build(){
    CM cm(states_no_, counters_no_, init_state_, alphabet_symbols_, tr_rel_, acc_);
    
    return move(cm);
  }


  
  CM CMParallel::parallel(const CM& cm1, const CM& cm2){
    assert(cm1.alphabet_symbols().size() == cm2.alphabet_symbols().size());
    
    uint counters_no1 = cm1.counters_no();
    state_t init_state1 = cm1.init_state();
    const vector<vector<vector<cm_pair>>>& tr_1 = cm1.tr();
    const set<state_t>& acc1 = cm1.accepting();

    uint states_no2 = cm2.states_no();
    uint counters_no2 = cm2.counters_no();
    state_t init_state2 = cm2.init_state();
    const vector<vector<vector<cm_pair>>>& tr_2 = cm2.tr();
    const set<state_t>& acc2 = cm2.accepting();

    // maps a pair c to a state in the parallel composition, such that
    // s1 = c/(size of cm2), s2 = c%(size of cm2).
    map<ullong, state_t> state_map; 
    uint counters_no = counters_no1 + counters_no2;
    state_t init_state = 0;
    const vector<string>& alphabet_symbols = cm1.alphabet_symbols();
    uint alpha_no = alphabet_symbols.size();
    ullong init_pair = init_state1*states_no2 + init_state2;
    state_map[init_pair] = init_state;
    
    // construct tr and accepting
    vector<vector<vector<cm_pair>>>tr {0, vector<vector<cm_pair>>{alpha_no}};
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

      for (uint a=0; a<alpha_no; a++){
	const vector<cm_pair>& cmv1 = tr_1[s1][a];	
	const vector<cm_pair>& cmv2 = tr_2[s2][a];

	for (auto it1=cmv1.begin(); it1!=cmv1.end(); it1++){
	  const cm_pair& cmp1 = *it1;
	  const CCSet& ccv1 = cmp1.first;
	  const MachineMove& mm1 = cmp1.second;
	  uint succ1 = mm1.state();
	  const vector<int>& add1 = mm1.addition();
	  
	  for (auto it2=cmv2.begin(); it2!=cmv2.end(); it2++){
	    const cm_pair& cmp2 = *it2;
	    const CCSet& ccv2 = cmp2.first;
	    const MachineMove& mm2 = cmp2.second;	    
	    uint succ2 = mm2.state();
	    const vector<int>& add2 = mm2.addition();

	    // combine the moves of the CMs
	    CCSet ccv {};
	    for (auto itc1=ccv1.begin(); itc1!=ccv1.end(); itc1++)
	      ccv.insert(*itc1);

	    auto itc2 = ccv2.begin();
	    for (uint i=0; itc2 != ccv2.end(); i++, itc2++){
	      const CounterConstraint& cc2 = *itc2;
	      CounterConstraint cc2new {counters_no1 + cc2.ctr_idx(),  cc2.op(), cc2.val()};
	      ccv.insert(cc2new);
	    }

	    vector<int> add (counters_no);
	    for (uint i=0; i<counters_no1; i++)
	      add[i] = add1[i];

	    for (uint i=0; i<counters_no2; i++)
	      add[i+counters_no1] = add2[i];

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
	    
	    MachineMove mm{succ, add};
	    cm_pair cmp = make_pair(ccv, mm);
	    if (succ >= tr.size()){
	      tr.push_back(vector<vector<cm_pair>>{alpha_no});
	      assert(succ <= tr.size());
	    }
	    
	    tr[s][a].push_back(cmp);
	    worklist.push_back(succ_pair);
	  }
	}
      }
    }

    CM cm {next_free, counters_no, init_state, alphabet_symbols, tr, acc};
#ifdef DEBUG
    assert(cm.check());
#endif
    
    return move(cm);
  }


  bool  IvPair::operator< (const IvPair& o) const {
    return (idx_ < o.idx_ || (idx_ == o.idx_ &&  val_ < o.val_));
  }


  MoveInfo Utils::getNumericConstrains(const CM& cm){
    set<IvPair> const_set;
    set<IvPair> iv_set;
    set<CCSet> cc_set;
    uint tr_size = 0;

    const vector<vector<vector<cm_pair>>> &tr = cm.tr();

    for (uint st=0; st<cm.states_no(); st++){
      const vector<vector<cm_pair>> & vs = tr[st];
      for (uint act=0; act<cm.alphabet_no(); act++){
	const vector<cm_pair> & va = vs[act];
       
	for (auto it=va.begin(); it!=va.end(); it++){
	  const CCSet& ccv = it->first;
	  const MachineMove& mm = it->second;
	  const vector<int>& addition = mm.addition();
	  for (uint i=0; i<addition.size(); i++){
	    IvPair ivp {i, addition[i]};
	    iv_set.insert(ivp);
	  }
	  tr_size++;
	  cc_set.insert(ccv);
	  for (auto itcc=ccv.begin(); itcc!=ccv.end(); itcc++){
	    const CounterConstraint& cc = *itcc;
	    IvPair ivp {cc.ctr_idx(), cc.val()};
	    const_set.insert(ivp);
	  }	  
	}
      }
    }

    return MoveInfo{tr_size, const_set, cc_set, iv_set};
  }
}
