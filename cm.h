/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef CM_H__
#define CM_H__

#include <utility>
#include "common.h"
#include "automata.h"

namespace fold {


  enum Operator {EQ, GT, LT, GEQ, LEQ, NEQ};

  
  class CounterConstraint {
  public:
    CounterConstraint(uint ctr_idx,
		      Operator op,
		      counter_t val);

    virtual ~CounterConstraint() { };

    uint ctr_idx() const 		{ return ctr_idx_; }
    Operator op() const 		{ return op_; }
    counter_t val() const		{ return val_; }
    inline bool satisfies(std::vector<counter_t> v) const;
    bool operator<(const CounterConstraint& o) const;

  private:
    const uint ctr_idx_;
    const Operator op_;
    const counter_t val_;
    friend std::ostream& operator<<(std::ostream& os, const CounterConstraint& cc);
  };

  typedef std::set<CounterConstraint> CCSet;

  // std::vector of counter constraints
  std::ostream& operator<<(std::ostream& os, const CCSet& ccv);  


  class MachineMove {
  public:
  MachineMove(state_t state, std::vector<int> addition)
    : state_{state}, addition_{addition}
    { }
    
    virtual ~MachineMove()			{ }
    state_t state() const 			{ return state_; }
    const std::vector<int>& addition() const 	{ return addition_; }

    MachineMove& operator=(const MachineMove& other);
    
  private:
    state_t state_;
    std::vector<int> addition_;
    friend std::ostream& operator<<(std::ostream& os, const MachineMove& mm);
  };


  // Represents a (std::vector of constraints, update) std::pair in a CM
  typedef std::pair<CCSet, MachineMove> cm_pair;

  
  // (Non-deterministic) counter machine. 
  class CM {
  public:
    // TODO use references in constructor
  CM(uint states_no,
     uint counters_no,
     state_t init_state,
     const std::vector<std::string>& alphabet_symbols,
     const std::vector<std::vector<std::vector<cm_pair>>>& tr_rel,
     const std::set<state_t>& acc)
    : states_no_{states_no}
    , counters_no_{counters_no}
    , init_state_{init_state}
    , alphabet_symbols_{alphabet_symbols}
    , tr_rel_{tr_rel}
    , acc_{acc}
    {}

    CM(CM &&other);
    CM(const CM& other);
    CM& operator=(CM&& other);
    CM& operator=(const CM& other);
      
    virtual ~CM() 					{ }
    uint states_no() const 			{ return states_no_;    }
    uint counters_no() const			{ return counters_no_;  }
    uint alphabet_no() const			{ return alphabet_symbols_.size(); }
    const std::vector<std::string>& alphabet_symbols() const	{ return alphabet_symbols_; }
    state_t init_state() const				{ return init_state_; }	
    const std::vector<std::vector<std::vector<cm_pair>>>& tr() const 	{ return tr_rel_;  }
    const std::set<state_t>& accepting() const		{ return acc_; }

    // Successors of the configuration after reading the symbol
    std::deque<cm_config> run(const cm_config& cnf, symbol_t s) const;

    // Returns the sequence of configuration after every step
    std::deque<std::deque<cm_config>> runAll(const std::vector<symbol_t>& word,
				   const std::vector<counter_t>& init_counters) const;

    std::deque<std::deque<cm_config>> runAll(const std::vector<std::string>& word,
				   const std::vector<counter_t>& init_counters) const;
        
    // Returns the configuration after reading the word from the initial configuration
    std::deque<cm_config> run(const std::vector<symbol_t>& word,
			 const std::vector<counter_t>& init_counters) const;

    std::deque<cm_config> run(const std::vector<std::string>& word,
			 const std::vector<counter_t>& init_counters) const;

    bool check() const;

  private:
    uint states_no_;
    uint counters_no_;
    state_t init_state_;
    std::vector<std::string> alphabet_symbols_;
    // state -> action -> (constraints x moves)
    // acion "one beyond alphabet size" is epsilon
    std::vector<std::vector<std::vector<cm_pair>>> tr_rel_;
    std::set<state_t> acc_;

    friend std::ostream& operator<<(std::ostream& os, const CM& cm);
  };


  // Constructor for CM
  class CMBuilder {
  public:
  CMBuilder(uint states_no, uint counters_no,
	    const std::vector<std::string>& alphabet_symbols)
    : states_no_{states_no}
    , counters_no_{counters_no}
    , init_state_{}
    , alphabet_symbols_{alphabet_symbols}
    , tr_rel_{states_no, std::vector<std::vector<cm_pair>>{alphabet_symbols.size()}}
    , acc_{}
    {}

    void setInitState(uint init)
    { init_state_ = init; }

    void addAccepting(state_t s)
    { acc_.insert(s); }

    bool addMove(state_t start, state_t target, uint symbol_id,
		 const CCSet& ccv, const std::vector<int>& addition);

    bool addMove(state_t start, state_t target, const std::string& action,
		 const CCSet& ccv, const std::vector<int>& addition);

    bool addMove(state_t start, state_t target, const std::string& action,
		 const CounterConstraint& cc, const std::vector<int>& addition);


    bool addMove(state_t start, state_t target, const std::string& action,
		 const std::vector<int>& addition);


    bool addSelfloop(state_t state);

    CM build();

  private:
    uint states_no_;
    uint counters_no_;
    state_t init_state_;
    std::vector<std::string> alphabet_symbols_;
    // state -> action -> (constraints x moves)
    std::vector<std::vector<std::vector<cm_pair>>> tr_rel_;
    std::set<state_t> acc_;
  };


  // Computes parallel composition of two CM's. The alphabets must be the same.
  class CMParallel {
  public:
    static CM parallel(const CM& cm1, const CM& cm2);
  };

  // Counter index, value std::pair
  class IvPair {
  public:
  IvPair(uint idx, int val) : idx_{idx}, val_{val}	{}
    virtual ~IvPair()						{}
    bool operator<(const IvPair& o) const;

    const uint idx_;
    const int val_;    
  };


  // Collection of information about CM moves and constraints.
  class MoveInfo {      
  public:

  MoveInfo(uint tr_size, std::set<IvPair> const_set,
	   std::set<CCSet> cc_set, std::set<IvPair> iv_set)
    : tr_size_{tr_size}, const_set_{const_set}, cc_set_{cc_set}, iv_set_{iv_set}
    { }

    virtual ~MoveInfo()			{ }
    const uint tr_size_; 			// number of transitions
    const std::set<IvPair> const_set_;  		// counter-constant in comparisons std::pairs
    const std::set<CCSet> cc_set_;			// counter constraints
    const std::set<IvPair> iv_set_;			// counter-update std::pairs    
  };



  class Utils {
  public:
    // Returns sorted lists of 1) numeric constraints in a CM, and 2)
    // index-update value pairs for counters.
    static MoveInfo getNumericConstrains(const CM& cm);

  };
}

#endif 
