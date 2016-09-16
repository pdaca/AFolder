/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <sstream>
#include <cassert>
#include <utility>
#include <iomanip>

#include "emptiness.h"
#include "graph.h"
#include "parikh.h"

using std::vector;
using std::set;
using std::deque;
using std::map;
using std::to_string;
using std::cout;
using std::endl;
using std::flush;
using std::move;
using std::pair;
using std::make_pair;
using std::setw;
using std::string;
using namespace z3;

namespace fold {

  // Returns the number of symbol ctr_i_u_j_l, where i is counter, u is a number, j is mode and l=0..1
  // no. =  iv* 2*nmax + 2j + l, where iv is the id of (i,u)-pair
  static uint to_ctr_id(uint iv, uint j, uint l, uint nmax){
    return iv*2*nmax + 2*j + l;
  }

  // Returns the number of (constraint z,j) symbol, 
  static uint to_con_id(uint z, uint j, uint nmax, uint ivmax){
    return z*nmax + j + ivmax*2*nmax;
  }

  // Returns the id of state (s,j)
  static uint to_state_id(uint s, uint j, uint nmax){
    return s * (nmax) + j;
  }

  // Returns the id of state (tr_id, j, l, i), where is tr_id is transition id in CM, j is mode number, l=0..1 and i=0 for constraint and 1<=i<k for counter i
  static uint to_state_act_id(uint tr_id, uint j, uint l, uint i,
		       uint nmax, uint k, uint states_no){
    assert(j < nmax && i < k && l <= 1);
    return states_no*nmax + tr_id*2*k*nmax + j*2*k + l*k + i;
  }

  // Map (p,a,q) transition to an unique value.
  static uint to_var_id(state_t p, symbol_t a, state_t q, uint states_no, uint alphabet_no){
    return p*states_no*alphabet_no + a*states_no + q;
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
	reg[i][j] = c.int_const(reg_name.c_str());
	string rev_name = "rev_" + to_string(i) +"_"+to_string(j)+postfix;
	rev[i][j] = c.int_const(rev_name.c_str());
	string arr_name = "arr_" + to_string(i) +"_"+to_string(j)+postfix;
	arr[i][j] = c.bool_const(arr_name.c_str());
	string sc_name = "sc_" + to_string(i) +"_"+to_string(j)+postfix;
	startc[i][j] = c.int_const(sc_name.c_str());
	string ec_name = "ec_" + to_string(i) +"_"+to_string(j)+postfix;
	endc[i][j] = c.int_const(ec_name.c_str());
      }
    }
  }



  // Add a formula, such that variable "out" contain the region id for variable "in" in the range [1,reg],
  // where reg is the region size for the for the counter
  static void addRegionFormula(context &c, solver &s,
			       const expr &in,
			       const expr& out,
			       const set<counter_t> const_set){
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


  // Add init formula.
  static void addInitFormula(context &c, solver& s, uint k, 
			     const vector<set<counter_t>>& comp_constants,
			     const vector<vector<expr>>& reg,
			     const vector<vector<expr>>& rev,
			     const vector<vector<expr>>& arr,
			     const vector<vector<expr>>& startc){
    for (uint j=0; j<k; j++){
      const set<counter_t>& const_set = comp_constants[j];
      const expr &rev_var = rev[j][0];
      s.add(rev_var == 0);

      const expr &reg_var = reg[j][0];
      const expr&  start_var = startc[j][0];
      addRegionFormula(c, s, start_var, reg_var, const_set);
    }

  }


  static void addRespectFormula(context &c, solver& s, uint k, uint nmax,
				const MoveInfo& mi,
				const vector<set<counter_t>> comp_constants,
				const vector<vector<expr>>& reg,
				const vector<vector<expr>>& rev,
				const vector<vector<expr>>& arr,
				const vector<vector<expr>>& startc,
				const vector<vector<expr>>& endc,
			        const vector<expr>& aparikh,
				const vector<vector<deque<UActionInfo>>>& update_info,
				const  vector<deque<CActionInfo>>& constraint_info){

    // incr[i][j] is the list of incrementing updates for counter i in mode j
    vector<vector<deque<uint>>> incr (k, vector<deque<uint>>(nmax)); 
    vector<vector<deque<uint>>> decr (k, vector<deque<uint>>(nmax)); 

    for (uint i=0; i<k; i++){
      for (uint j=0; j<nmax; j++){
	const deque<UActionInfo>& dap = update_info[i][j];

	for(auto it=dap.begin(); it!=dap.end(); it++){
	  int u = it->val_;
	  uint idx = it->index_;

	  if (u>0){
	    incr[i][j].push_back(idx);
	  }
	  if (u<0){
	    decr[i][j].push_back(idx);
	  }
	}
      }
    }

    // when non-incrementing (non-decrementing) allow only certain updates
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax; i++){
    	const expr& arr_var = arr[j][i];

	const deque<uint> incr_deq = incr[j][i];
	if (!incr_deq.empty()){
	  expr inf = c.bool_val(true);
		
	  for (auto it = incr_deq.begin(); it!=incr_deq.end(); it++){
	    uint id = *it;
	    const expr& avar = aparikh[id];	  
	    inf = inf && (avar == 0);
	  }
	  s.add(implies(arr_var, inf));
	}

	const deque<uint> decr_deq = decr[j][i];
	if (!decr_deq.empty()){
	  expr def = c.bool_val(true);
		
	  for (auto it = decr_deq.begin(); it!=decr_deq.end(); it++){
	    uint id = *it;
	    const expr& avar = aparikh[id];	  
	    def = def && (avar == 0);
	  }
	  s.add(implies(!arr_var, def));
	}
      }
    }
    
    // constraints for the start and end counter values in each mode
    for (uint i=0; i<k; i++){
   
      for (uint j=0; j<nmax; j++){
	// counter at the start 
	const expr &start_var = startc[i][j];
	
	if (j == 0){
	  //s.add(start_var == ((int) init));
	} else {
	  const expr &end_prev_var = endc[i][j-1];
	  expr sum = c.int_val(0);
	  
	  const deque<UActionInfo>& deq = update_info[i][j-1];
	  for (auto it=deq.begin(); it!=deq.end(); it++){
	    uint indx = it->index_;
	    uint l = it->l_;
	    int d = it->val_;
	    if (l == 1 && d != 0){
	      expr a_var = aparikh[indx];
	      sum = sum + (d * a_var);
	    }
	  }
	  s.add(start_var == end_prev_var + sum);
	}

	// counter at the end
	const expr &end_var = endc[i][j];
	const deque<UActionInfo>& deq = update_info[i][j];
	expr sum = c.int_val(0);
	for (auto it=deq.begin(); it!=deq.end(); it++){
	  int d = it->val_;
	  uint indx = it->index_;
	  uint l = it->l_;
	  if (l == 0 && d != 0){
	    expr a_var = aparikh[indx];
	    sum = sum + (d * a_var);
	  }
	}
	
	s.add(end_var == start_var + sum);
      }
    }

    // constraints that related start and end counter values to their regions	
    for (uint j=0; j<k; j++){
      const set<counter_t>& const_set = comp_constants[j];
      
      for (uint i=0; i<nmax; i++){
	const expr& reg_var = reg[j][i];
	const expr& start_var = startc[j][i];
	const expr& end_var = endc[j][i];
	addRegionFormula(c, s, start_var, reg_var, const_set);
	addRegionFormula(c, s, end_var, reg_var, const_set);	  
      }
    }

    // constraint that start counters satisfy executed counter tests
    for (uint i=0; i<nmax; i++){
      const deque<CActionInfo>& deq = constraint_info[i];
      for (auto it=deq.begin(); it!=deq.end(); it++){
	const CCSet& ccv = it->ccv_;
	uint indx = it->index_;

	// build a formula for the counter constraint
	for (auto itc=ccv.begin(); itc!=ccv.end(); itc++){
	  const CounterConstraint& cc = *itc;
	  uint ctr_idx = cc.ctr_idx();
	  int val = (int) cc.val();
	  const expr& start_var = startc[ctr_idx][i];
	  const expr& a_var = aparikh[indx];

	  switch (cc.op()){
	  case EQ:
	    s.add(implies(a_var > 0, start_var == val)); 
	    break;
	
	  case GT:
	    s.add(implies(a_var > 0, start_var > val)); 
	    break;

	  case LT:
	    s.add(implies(a_var > 0, start_var < val)); 
	    break;

	  case GEQ:
	    s.add(implies(a_var > 0, start_var >= val)); 
	    break;

	  case LEQ:
	    s.add(implies(a_var > 0 , start_var <= val)); 
	    break;

	  };
	 
	}
      }
    }

    // require counters and the start and end of modes to be non-zero
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax; i++){
	const expr &start_var = startc[j][i];
	const expr &end_var = endc[j][i];
	s.add(start_var >= 0);
	s.add(end_var >= 0);
      }
    }    
  }


  static  void  addGoodSeqFormula(context &c, solver &s,
				  uint k, uint nmax,
				  uint r,
				  vector<set<counter_t>>& comp_constants,
				  const vector<vector<expr>>& reg,
				  const vector<vector<expr>>& rev,
				  const vector<vector<expr>>& arr){
    // constraint rev[j][i] to the range [0, r] and reg[i][j] is in
    // the range [1, reg_no], where reg_no is the number of regions
    // for the counter
    
    for (uint j=0; j<k; j++){
      set<counter_t> const_set = comp_constants[j];
      // TODO reg formula not precise, and probably not even usefull
      // int reg_no = const_set.size()>0 ? 2*const_set.size() : 1;
      
      for (uint i=0; i<nmax; i++){
	const expr &rev_var = rev[j][i];
	s.add(rev_var >= 0);
	s.add(rev_var <= ((int) r));
	// const expr &reg_var = reg[j][i];
	// s.add(1 <= reg_var);
	// s.add(reg_var <= reg_no);
      }
    }
    
    // change in direction increase the number of reversals
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax-1; i++){
	const expr &rev_var = rev[j][i];
	const expr &rev_next_var = rev[j][i+1];
	const expr &arr_var = arr[j][i];
	const expr &arr_next_var = arr[j][i+1];
	s.add(implies(arr_var != arr_next_var, rev_next_var == (rev_var + 1 )));
	s.add(implies(arr_var == arr_next_var, rev_next_var == rev_var));
      }
    }


    // relate arr to the changes in reg
    for (uint j=0; j<k; j++){
      for (uint i=0; i<nmax-1; i++){
	const expr &reg_var = reg[j][i];
	const expr &reg_next_var = reg[j][i+1];
	const expr &arr_next_var = arr[j][i+1];
	s.add(implies(reg_var < reg_next_var, !arr_next_var));
	s.add(implies(reg_var > reg_next_var, arr_next_var));
      }
    }
  }


  HagueEmptinessCheck::HagueEmptinessCheck (HagueEmptinessCheck&& other)
    : k_ {other.k_}
    , nmax_{other.nmax_}
    , reg_{move(other.reg_)}
    , rev_{move(other.rev_)}
    , arr_{move(other.arr_)}
    , startc_{move(other.startc_)}
    , endc_{move(other.endc_)}
    , aparikh_{move(other.aparikh_)}
    , flow_map_{move(other.flow_map_)}
    , symbol_info_{move(other.symbol_info_)}
    , nfa_{move(other.nfa_)}
    {}


  HagueEmptinessCheck& HagueEmptinessCheck::operator=(HagueEmptinessCheck&& other){
    k_			= other.k_;
    nmax_		= other.nmax_;
    reg_		= move(other.reg_);
    rev_		= move(other.rev_);
    arr_		= move(other.arr_); 
    startc_		= move(other.startc_);
    endc_		= move(other.endc_);
    aparikh_		= move(other.aparikh_);
    flow_map_		= move(other.flow_map_);
    symbol_info_ 	= move(other.symbol_info_);
    nfa_		= move(other.nfa_);
    return *this;
  }


  HagueEmptinessCheck::HagueEmptinessCheck (const HagueEmptinessCheck& other)
    : k_ {other.k_}
    , nmax_{other.nmax_}
    , reg_{other.reg_}
    , rev_{other.rev_}
    , arr_{other.arr_}
    , startc_{other.startc_}
    , endc_{other.endc_}
    , aparikh_{other.aparikh_}
    , flow_map_{other.flow_map_}
    , symbol_info_{other.symbol_info_}
    , nfa_{other.nfa_}
    {}


  HagueEmptinessCheck& HagueEmptinessCheck::operator=(const HagueEmptinessCheck& other){
    k_			= other.k_;
    nmax_		= other.nmax_;
    reg_		= other.reg_;
    rev_		= other.rev_;
    arr_		= other.arr_; 
    startc_		= other.startc_;
    endc_		= other.endc_;
    aparikh_		= other.aparikh_;
    flow_map_		= other.flow_map_;
    symbol_info_ 	= other.symbol_info_;
    nfa_		= other.nfa_;
    return *this;
  }


  
  static uint regionsNo(const set<counter_t>& comp_constants){
    uint r = comp_constants.size();
    if (r == 0)
      return 1;
    
    auto it=comp_constants.begin();
    counter_t prev = *it;
    if (prev > 0)
      r++;	
    it++;
      
    for(; it!=comp_constants.end(); it++){
      counter_t curr = *it;
      if (curr > prev + 1)
	r++;
      prev = curr;
    }
    return r+1;
  }

  
  void HagueEmptinessCheck::addEmptinessFormula(context&  c, solver& s,
				    const CM& cm, uint r,
				    string postfix){
    // TODO use region for each counter
    k_ = cm.counters_no();
    MoveInfo mi = Utils::getNumericConstrains(cm);

    vector<set<counter_t> > comp_constants(k_);      // constants in for each counter
    const set<IvPair>& const_set = mi.const_set_;
  
    for (auto it=const_set.begin(); it!=const_set.end(); it++){
      const IvPair& ivp = *it;
      uint idx = ivp.idx_;
      set<counter_t>& cnst = comp_constants[idx];
      cnst.insert(ivp.val_);
    }

    uint movesno = 0;		// number of move changes per reversal
    vector<uint> moves (k_);
    for (uint i=0; i<k_; i++){
      moves[i] = regionsNo(comp_constants[i]);
      movesno += moves[i]-1;
    }

    nmax_ = 1+movesno*(r+1);

#ifdef INFO
    cout << "Check emptiness Hague k="<< k_ << ", r=" << r << ", moves per counter=" << moves
	 << ", nmax=" << nmax_ << ", tr_size= " << mi.tr_size_ << endl;
    cout << "constants: ";
    for (auto it=const_set.begin(); it!=const_set.end(); it++)
            cout <<  "(" << it->idx_ << "," << it->val_  << "), ";
    cout << endl;
    
    for (uint i=0; i<k_; i++){
      if (comp_constants[i].empty())
	continue;
      cout << "\t- counter " <<  i << ":";
      for (auto it=comp_constants[i].begin(); it!=comp_constants[i].end(); it++)
	cout << *it << ", ";
      cout << endl;
    }
    
    cout << "constraints : ";    
    for (auto it=mi.cc_set_.begin(); it!=mi.cc_set_.end(); it++)
      cout <<  *it << ", ";
    cout << endl << "iv-pairs : ";
    for (auto it=mi.iv_set_.begin(); it!=mi.iv_set_.end(); it++)
      cout <<  "(" << it->idx_ << "," << it->val_  << "), ";
    cout << endl << endl;
#endif

    // create mode variables
    expr ff =  c.bool_val(false);
    reg_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff)); // reg_[j][i] is reg_j^i
    rev_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff));
    arr_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff));
    startc_ = vector<vector<expr>> (k_,vector<expr>(nmax_, ff));
    endc_ = vector<vector<expr>>(k_,vector<expr>(nmax_, ff));
    createModeVars(c, k_,nmax_, postfix, reg_, rev_, arr_, startc_, endc_);

    // create NFA
    vector<vector<deque<UActionInfo>>> update_info (k_,vector<deque<UActionInfo>>(nmax_));
    vector<deque<CActionInfo>> constraint_info (nmax_);
    map<uint, map<uint, uint>> si;
    symbol_info_ = si;

    
    nfa_ = toNFA(cm, mi, r, update_info, constraint_info, symbol_info_);
    uint alpha_nfa_no = nfa_.alphabet_no();

    // create parikh variables
    expr zero = c.int_val(0);
    aparikh_ = vector<expr> (alpha_nfa_no, zero);
    for (uint i=0; i<alpha_nfa_no; i++){
      string name = "a_" + to_string(i) + postfix;
      aparikh_[i] = c.int_const(name.c_str());
    }

    addParikhFormula(c, s, nfa_, aparikh_, postfix, flow_map_);
    addInitFormula(c, s, k_, comp_constants, reg_, rev_, arr_, startc_);
    addGoodSeqFormula(c, s, k_, nmax_, r, comp_constants, reg_, rev_, arr_);
    addRespectFormula(c, s, k_, nmax_, mi, comp_constants, reg_, rev_, arr_,
		      startc_, endc_, aparikh_, update_info, constraint_info);
    // addEndValFormula not needed
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
	const expr& var = vars[j][i];
	os << setw(WIDTH) << model.eval(var) << "|";
      }
      os << endl;
    }
  }
  

  void HagueEmptinessCheck::printModel(const model& model, std::ostream& os){
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
      const expr& var = aparikh_[i];
      os << alphabet_symbols[i] << " = " << model.eval(var) << endl;
    }
#endif
  }

  


  
    // Construct a weighted graph from the NFA and the model.  The
    // graph consists of the NFA states, and the weighted of edges is
    // taken from the model.
  static WeightedLabeledGraph<string> constructGraph(const model& model,
						     const CM& cm,
						     const NFA &nfa,
						     uint nmax,
						     const map<uint, expr>& flow_map,
						     const map<uint, map<uint, uint>>& symbol_info){
    uint states_no = nfa.states_no();
    vector<vector<uint>> weight (states_no, vector<uint>(states_no, 0));
    vector<vector<int>> labels (states_no, vector<int>(states_no, -1));
    const vector<string>& alphabet_symbols = cm.alphabet_symbols();

    uint states_nfa_no = nfa.states_no();
    uint alphabet_nfa_no = nfa.alphabet_no();
    const vector<vector<vector<state_t>>>& tr_nfa = nfa.tr();

    for (uint p=0; p<states_no; p++){
      for (uint a=0; a<alphabet_nfa_no; a++){
	const vector<state_t>& succ = tr_nfa[p][a];
	for (auto it=succ.begin(); it!=succ.end(); it++){
	  state_t q=*it;
	  
	  uint id = to_var_id(p,a,q,states_nfa_no, alphabet_nfa_no);
	  auto elem = flow_map.find(id);
	  if (elem == flow_map.end())
	    assert(false);
	  const expr& flow_var = elem->second;
	  uint flow =  getZ3Value(model, flow_var);
	  weight[p][q] = flow;

	  auto pelem = symbol_info.find(p);
	  if (pelem != symbol_info.end()){
	    const map<uint, uint> pmap = pelem->second;

	    auto qelem = pmap.find(q);
	    if (qelem != pmap.end()){
	      uint sid = qelem->second;
	      labels[p][q] = sid;	      
	    }
	  }
	}
      }
    }

    WeightedLabeledGraph<string> graph(states_no, weight, labels, alphabet_symbols);

    return move(graph);
  }


					     
					     
  
  vector<string> HagueEmptinessCheck::wordFromModel(const model& model, const CM& cm) {
    WeightedLabeledGraph<string> graph = constructGraph(model, cm, nfa_, nmax_,
						flow_map_, symbol_info_);

    uint start = to_state_id(nfa_.init_state(), 0, nmax_);
    const vector<vector<int>>& label = graph.label_;
    const vector<string>&  alphabet = graph.alphabet_symbols_;

    // cout << "Graph" << endl;
    // cout << graph << endl;

    deque<uint> epath = getEulerianPath<string>(graph, start); 

    vector<string> word;
    int p = -1;
    for (auto it=epath.begin(); it!=epath.end(); it++){
      uint q = *it;
      
      if (p!=-1){
	int s = label[p][q];
	if (s >= 0)
	  word.push_back(alphabet[s]);  
      }
      p = q;
    }

    
    return word;
  }



  static void constructNFAAlphabet(const CM& cm, const MoveInfo& mi, const uint nmax,
				   vector<string>& alphabet,
				   vector<vector<deque<UActionInfo>>>& update_info,
				   vector<deque<CActionInfo>>& constraint_info){
    
    // Construct the alphabet for ther NFA
    const set<CCSet> & cc_set = mi.cc_set_;
    const set<IvPair> & iv_set = mi.iv_set_;
    uint ivmax = iv_set.size();
    
    uint i=0;
    for (auto it_iv = iv_set.begin(); it_iv!=iv_set.end(); it_iv++, i++) {
      for (uint j=0; j<nmax; j++){
	for (uint l=0; l<=1; l++){
	  uint id = to_ctr_id(i, j, l, nmax);
	  uint cindx = it_iv->idx_;
	  int u = it_iv->val_;
	  string str = "ctr" + to_string(cindx) + "_" + to_string(u) + "_" + to_string(j) + "_" + to_string(l);
	  alphabet[id] = str;
	  UActionInfo ap {u, id, l};
	  update_info[cindx][j].push_back(ap);
	}
      }
    }
    
    i=0;
    for (auto it_cc=cc_set.begin(); it_cc!=cc_set.end(); it_cc++, i++){
      for (unsigned j=0; j<nmax; j++){
	std::stringstream sstm;
	sstm << *it_cc;
	string str = sstm.str() + "_" + to_string(j);
	unsigned id = to_con_id(i,j,nmax,ivmax);
	alphabet[id] = str;
	CActionInfo ca {*it_cc, id};
	constraint_info[j].push_back(ca);
      }
    }
  }

  // Construct transition relation for the NFA
  static void constructNFAtr(const CM& cm, const MoveInfo& mi, uint nmax,
			     uint ivmax,
			     const vector<string>& alphabet,
			     vector<vector<vector<state_t>>>& tr,
			     const map<CCSet, uint>& cc_map,
			     const map<IvPair, uint>& iv_map,
			     map<uint,map<uint, uint>>& symbol_info){

    uint k = cm.counters_no();
    uint states_cm_no = cm.states_no();
    const vector<vector<vector<cm_pair>>>& tr_cm = cm.tr();

    uint tr_id = 0;
    
    for (uint s=0; s<states_cm_no; s++){
      const vector<vector<cm_pair>>& vs = tr_cm[s];
      
      for (uint act=0; act<cm.alphabet_no(); act++){
	const vector<cm_pair> & va = vs[act];
	
	for (auto it=va.begin(); it!=va.end(); it++, tr_id++){
	  const CCSet& ccv = it->first;
    	  const MachineMove& mm = it->second;
	  const vector<int> addition = mm.addition();
	  state_t succ = mm.state();
	  auto ccv_elem = cc_map.find(ccv);
	  if (ccv_elem == cc_map.end()){
	    assert(false);
	  }
	  uint ccv_id = ccv_elem->second;

// #ifdef DEBUG
// 	  const vector<string>& alphabet_cm = cm.alphabet_symbols();
// 	  cout << "CM transition: s=" << s << ", act=" << alphabet_cm[act] << ", " << mm 
// 	       << endl << endl;
// #endif
	  
    	  for (uint j=0; j<nmax; j++){
	    for (uint l=0; l<=1; l++){
	      
	      if (j==nmax-1 && l==1)
		break;
	      
	      // add an action for the constraint
	      state_t s_nfa = to_state_id(s,j,nmax);
	      uint act_id = to_con_id(ccv_id,j,nmax, ivmax); 
	      state_t s_con_nfa = to_state_act_id(tr_id, j, l, 0, nmax, k, states_cm_no);
	      vector<state_t>& v = tr[s_nfa][act_id];
	      v.push_back(s_con_nfa);
	      symbol_info[s_nfa][s_con_nfa] = act;

// #ifdef DEBUG
// 	      cout << "(s=" << s << ",j=" << j << ")=" << s_nfa
// 		   << " -- act=" << alphabet[act_id] << " -! "
// 		   << "(tr_id=" << tr_id << ",j=" << j << ",l=" << l << ",i=0)=" << s_con_nfa
// 		   << endl;
// #endif
	   
	      // add actions for counter updates
	      uint s_prev_nfa = s_con_nfa;
	      for (uint i=0; i<k-1; i++){
		if (addition[i] == 0)
		  continue; // this action has no effect
		
		IvPair ivp {i,addition[i]};
		auto iv_elem = iv_map.find(ivp);
		if (iv_elem == iv_map.end())
		  assert(false);
		uint iv_id = iv_elem->second;
		uint act_idu = to_ctr_id(iv_id, j, l, nmax);
		uint s_ctr_nfa = to_state_act_id(tr_id, j, l, i+1, nmax, k, states_cm_no);
		vector<state_t>& vap = tr[s_prev_nfa][act_idu];
		vap.push_back(s_ctr_nfa);

// #ifdef DEBUG
// 	      cout << s_prev_nfa 		
// 		   << " -- act=" << alphabet[act_idu] << " -- "
// 		   << "(tr_id=" << tr_id << ",j=" << j << ",l=" << l << ",i=" << (i+1) << ")=" << s_ctr_nfa
// 		   << endl;
// #endif
	      s_prev_nfa = s_ctr_nfa;
	      }

	      IvPair ivp {k-1,addition[k-1]};
	      auto iv_elem = iv_map.find(ivp);
	      if (iv_elem == iv_map.end())
		assert(false);
	      uint iv_id = iv_elem->second;
	      act_id = to_ctr_id(iv_id, j, l, nmax);
	      uint succ_nfa = to_state_id(succ,j+l,nmax);
	      vector<state_t>& vl = tr[s_prev_nfa][act_id];
	      vl.push_back(succ_nfa);
// #ifdef DEBUG
// 	      cout << s_prev_nfa
// 		   << " -- act=" << alphabet[act_id] << " -- "
// 		   << "(s=" << succ << ",j=" << (j+l) << ")=" <<  succ_nfa 
// 		   << endl << endl;
// #endif
	    }
	  }
// #ifdef DEBUG
// 	  cout << "-----------" << endl;
// #endif
    	}	
      }
    }
  }
  
  
  NFA HagueEmptinessCheck::toNFA(const CM& cm, const MoveInfo& mi, uint r,
				 vector<vector<deque<UActionInfo>>>& update_info,
				 vector<deque<CActionInfo>>& constraint_info,
				 map<uint, map<uint, uint>>& symbol_info){
    uint k = cm.counters_no();
    uint states_cm_no = cm.states_no();
    const set<CCSet>& cc_set = mi.cc_set_;
    const set<IvPair> & iv_set = mi.iv_set_;
    const uint tr_cm_no = mi.tr_size_;

    uint ivmax = iv_set.size();

    // map updates and constraints in CM to numbers
    map<IvPair, uint> iv_map;
    map<CCSet, uint> cc_map;

    uint c=0;
    for (auto it = iv_set.begin(); it!=iv_set.end(); it++, c++){
      iv_map[*it] = c;
    }

    c=0;
    for (auto it = cc_set.begin(); it!=cc_set.end(); it++, c++){
      cc_map.insert(make_pair(*it,c));
    }

    // construct alphabet
    uint alphabet_size = iv_set.size() * nmax_ * 2 + cc_set.size() * nmax_;
    vector<string> alphabet (alphabet_size); 
    constructNFAAlphabet(cm, mi, nmax_, alphabet, update_info, constraint_info);

    // construct transition relation
    uint states_no = to_state_act_id(tr_cm_no-1, nmax_-1, 1, k-1, nmax_, k, states_cm_no)+1;
    vector<vector<vector<state_t>>> tr (states_no, vector<vector<state_t>>(alphabet.size()));
    constructNFAtr(cm, mi, nmax_, ivmax, alphabet, tr, cc_map, iv_map, symbol_info);
 
    // construct initial and accepting states for the NFA
    state_t init = to_state_id(cm.init_state(), 0, nmax_);
    set<state_t> acc;
    const set<state_t> & acc_cm = cm.accepting();

    for (state_t s = 0; s <  states_cm_no; s++){
      if (acc_cm.find(s) != acc_cm.end()){
	for (uint j=0; j<nmax_; j++){
	  uint id = to_state_id(s,j,nmax_);
	  acc.insert(id);
	}
      }
    }
    
    NFA control_nfa {states_no, init, alphabet, tr, acc};

#ifdef DEBUG
    cout << endl;
    //    cout << "tr_id=" << tr_id << ", tr_cm_no=" << tr_cm_no << endl;
    cout << "NFA states no=" << states_no << endl;
    //cout << control_nfa << endl;
    assert(control_nfa.check());
#endif
    
    return move(control_nfa);
  }







}



