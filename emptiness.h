/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef EMPTINESS_H__
#define EMPTINESS_H__

#include <map>
#include <set>
#include <utility>
#include "common.h"
#include "automata.h"
#include "cm.h"
#include "z3++.h"

namespace fold {

  // Info about an action that represents an update of a counter
  class UActionInfo {
  public:
    UActionInfo(int val, uint index, uint l)
      : val_{val}, index_{index}, l_{l}
    {};

    const int val_;
    const uint index_;
    const uint l_;
  };


  // Info about an action that represents a constraint
  class CActionInfo {
  public:
    CActionInfo(const CCSet& ccv, uint index)
      : ccv_{ccv}, index_{index}
    {};

    const CCSet ccv_;
    const uint index_;
  };

 
  
  // Procedure from "Model checking recursive program with numerical
  // data types" Hague'11.
  class HagueEmptinessCheck  {
  public:
  HagueEmptinessCheck()
    : k_{0}
    , nmax_{0}
    , reg_{}
    , rev_{}
    , arr_{}
    , startc_{}
    , endc_{}
    , aparikh_{}
    , flow_map_{}
    , symbol_info_{}
    , nfa_{}
    {};
    
    virtual ~HagueEmptinessCheck()		{};

    HagueEmptinessCheck(HagueEmptinessCheck&& other);
    HagueEmptinessCheck& operator=(HagueEmptinessCheck&& other);
    HagueEmptinessCheck(const HagueEmptinessCheck& other);
    HagueEmptinessCheck& operator=(const HagueEmptinessCheck& other);
    
    // Adds a Pressburger constraint that is satisfiable if the
    // counter machine with r reversal has an non-empty language. The
    // postfix is appended to every variable name.
    void addEmptinessFormula(z3::context& c, z3::solver& s, const CM& cm,
			     uint r, std::string postfix);


    // Prints to the stream a model for an emptiness formula.
    void printModel(const z3::model& model, std::ostream& os);

    // Generate word in the language of the CM from a model.
    std::vector<std::string> wordFromModel(const z3::model& model, const CM& cm);

    uint k()				{ return k_; }
    uint nmax()				{ return nmax_; }
    const std::vector<std::vector<z3::expr>>& reg()		{ return reg_; }
    const std::vector<std::vector<z3::expr>>& rev()		{ return rev_; } 
    const std::vector<std::vector<z3::expr>>& arr()		{ return arr_; } 
    const std::vector<std::vector<z3::expr>>& startc()	{ return startc_; }
    const std::vector<std::vector<z3::expr>>& endc()		{ return endc_; }
    const std::vector<z3::expr>& aparikh()		{ return aparikh_; }
    const std::map<uint, z3::expr>& flow_map()	{ return flow_map_; }
    const std::map<uint,
      std::map<uint, uint>>& symbol_info() 	{ return symbol_info_ ;}
    const NFA& nfa()				{ return nfa_; }
    // Initial value of counter i
    const z3::expr& start(uint i)	{ return startc_[i][0]; }
    // End value of counter i
    const z3::expr& end(uint i)		{ return endc_[i][nmax_-1]; }

    private:
      uint k_;
      uint nmax_;
      std::vector<std::vector<z3::expr>> reg_;
      std::vector<std::vector<z3::expr>> rev_; 
      std::vector<std::vector<z3::expr>> arr_; 
      std::vector<std::vector<z3::expr>> startc_;
      std::vector<std::vector<z3::expr>> endc_;
      std::vector<z3::expr> aparikh_;
      std::map<uint, z3::expr> flow_map_;
      std::map<uint, std::map<uint, uint>> symbol_info_;
      NFA nfa_;

      NFA toNFA(const CM& cm, const MoveInfo& mi, uint rev,
		// update_info[j][i] is a list of update actions for
		// counter j in mode i
		std::vector<std::vector<std::deque<UActionInfo>>>& update_info,
		// constraint_info[i] is the list of constraint actions
		// in mode i
		std::vector<std::deque<CActionInfo>>& constraint_info,
		// alphabet_map[p][q] = i if: i) p is a state of the
		// NFA that maps to a state of the CM, ii) (p,.,q) is an
		// transition in the NFA, and iii) i is the index of
		// alphabet symbol in the CM
		std::map<uint, std::map<uint, uint>>& symbol_info);
  };

}

#endif
