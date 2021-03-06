/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef SEMPTINESS_H__
#define SEMPTINESS_H__

#include <map>
#include <set>
#include <utility>
#include "common.h"
#include "automata.h"
#include "scm.h"
#include "semptinessaux.h"

namespace fold {



  // Extended version of the procedure from "Model checking recursive
  // program with numerical data types" Hague'11.
  template <typename T>
  class SCMEmptinessCheck  {
  public:
  SCMEmptinessCheck(const SCM<T>& cm)
    : cm_ {cm}
    , nfa_{}    
    , k_{cm.counters_no()}
    , nmax_{0}
    , reg_{}
    , rev_{}
    , arr_{}
    , startc_{}
    , endc_{}
    , aparikh_{}
    , scons_{}
    , scons_srt_{}
    , regions_{}
    , flow_map_{}
    , sum_map_{}
    , action_map_{}
    {};
    
    virtual ~SCMEmptinessCheck()		{};

    // Adds a Pressburger constraint that is satisfiable if the
    // counter machine with r reversal has an non-empty language. The
    // postfix is appended to every variable name.
    void addEmptinessFormula(z3::solver& s, uint r, std::string postfix);

    // Prints to the stream a model for an emptiness formula. 
    void printModel(const z3::model& model, std::ostream& os);

    // Generate word in the language of the CM from a model.
    std::vector<CmAction> wordFromModel(const z3::model& model);

    // Generates a word of concrete values, provided the alphabet of
    // CM is symbolic formulas
    std::vector<int> ewordFromModel(const z3::model& model);
    

    const SCM<T> cm() const						{ return cm_; }
    uint k() const							{ return k_; }
    uint nmax() const							{ return nmax_; }
    const std::vector<std::vector<z3::expr>>& reg() const		{ return reg_; }
    const std::vector<std::vector<z3::expr>>& rev() const		{ return rev_; } 
    const std::vector<std::vector<z3::expr>>& arr() const		{ return arr_; } 
    const std::vector<std::vector<z3::expr>>& startc() const		{ return startc_; }
    const std::vector<std::vector<z3::expr>>& endc() const		{ return endc_; }
    const std::vector<z3::expr>& aparikh() const			{ return aparikh_; }
    const std::vector<z3::expr>& scons() const				{ return scons_; }
    const std::vector<std::vector<z3::expr>>& scons_srt() const		{ return scons_srt_; }
    const std::vector<std::list<Region>>& regions() const		{ return regions_; }
    const std::map<std::pair<state_t, NfaAction>, z3::expr>& flow_map() const
      { return flow_map_; }
    const std::map<std::pair<uint, std::pair<state_t, NfaAction> >, z3::expr>& sum_map() const
      { return sum_map_; }
    const NFA<CmAction>& nfa() const					{ return nfa_; }
    // Initial value of counter i
    const z3::expr& start(uint i) const		      			{ return startc_.at(i).at(0); }
    // End value of counter i
    const z3::expr& end(uint i)	const					{ return endc_.at(i).at(nmax_-1); }

  private:
    SCM<T> cm_;
    NFA<CmAction> nfa_;
    uint k_;
    uint nmax_;
    std::vector<std::vector<z3::expr>> reg_;
    std::vector<std::vector<z3::expr>> rev_; 
    std::vector<std::vector<z3::expr>> arr_; 
    std::vector<std::vector<z3::expr>> startc_;
    std::vector<std::vector<z3::expr>> endc_;
    std::vector<z3::expr> aparikh_;
    std::vector<z3::expr> scons_;							// unsorted symbolic constants
    std::vector<std::vector<z3::expr>> scons_srt_;				      	// sorted symbolic constants per counter
    std::vector<std::list<Region>> regions_;						// set of regions for each counter
    std::vector<z3::expr> svars_;							// variables that express symbol values
    std::map<std::pair<state_t, NfaAction>, z3::expr> flow_map_;			// variables for actions' Parikh image
    std::map<std::pair<uint, std::pair<state_t, NfaAction>>, z3::expr> sum_map_;	// variables for actions' total sum
    std::map<std::pair<state_t, NfaAction>,std::pair<state_t, CmAction>> action_map_; 

  };


}
#endif
