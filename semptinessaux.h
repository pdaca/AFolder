/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef SEMPTINESSAUX_H__
#define SEMPTINESSAUX_H__

#include <map>
#include <set>
#include <utility>
#include <list>
#include "common.h"
#include "automata.h"
#include "graph.h"
#include "scm.h"

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

  // Info about an action that represents a constraint
  class SCActionInfo {
  public:
  SCActionInfo(const std::set<SCounterConstraint>& ccv, uint index)
    : ccv_{ccv}
    , index_{index}
    {};

    const std::set<SCounterConstraint> ccv_;
    const uint index_;
  };


  // Represents a counter region
  class Region {
  public:
  Region(const Constant& l_cnst,
	 bool l_incl,
	 bool l_isinf,
	 const Constant& u_cnst,
	 bool u_incl,
	 bool u_isinf)
    : l_cnst_ {l_cnst}
    , l_incl_ {l_incl}
    , l_isinf_ {l_isinf}
    , u_cnst_ {u_cnst}
    , u_incl_ { u_incl}
    , u_isinf_ {u_isinf}
    {};

    ~Region()	{};
    
    const Constant l_cnst_;  	// the lower bound
    bool l_incl_;	      	// is the lower bound included
    bool l_isinf_;		// true if the lower bound is -infinity, overrides the constant
    const Constant u_cnst_;	// the upper bound
    bool u_incl_;		// is the upper bound included
    bool u_isinf_;		// true if the upper bound is +infinity, overrides the constant

    friend std::ostream& operator<<(std::ostream& os,
				    const Region& reg);
  };


  std::ostream& operator<<(std::ostream& os, const std::list<Region>& regs);
  

  struct ConstOperatorCmp
  {
    bool operator()(const std::pair<Constant, Operator>& a, const std::pair<Constant, Operator>& b) const
    {
      if (a.first < b.first)
	return true;

      if (b.first < a.first)
	return false;

      if (a.second < b.second)
	return true;

      return false;      
    }
  };



  
  // Compute regions for the counter
  void regionsNo(uint i,
		 const std::vector<z3::expr>& scons_srt_ctr,
		 const SCMInfo& info,
		 std::list<Region>& regs);


  void printVars(const z3::model &model,
		 std::ostream& os,
		 uint k,
		 uint nmax,
		 uint WIDTH,
		 const std::vector<std::vector<z3::expr>>& vars, 
		 std::string name);


  // Construct a weighted graph from the NFA and the model.  The
  // graph consists of the NFA states, and the weighted of edges is
  // taken from the model.
  WeightedLabeledGraph<uint> constructGraph(const z3::model& model,
					    const NFA<CmAction>& nfa,
					    uint nmax,
					    const std::map<std::pair<state_t, NfaAction>, z3::expr>& flow_map,
					    const std::map<std::pair<state_t, NfaAction>,std::pair<state_t, CmAction>>& action_map);


  template <typename T>
    NFA<CmAction> toNFA(const SCM<T>& cm,
			uint nmax,
			std::map<std::pair<state_t, NfaAction>,std::pair<state_t, CmAction>>& action_map);



}
#endif
