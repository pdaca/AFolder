/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef SCM_H__
#define SCM_H__

#include <utility>
#include "common.h"
#include "automata.h"
#include "cm.h"

namespace fold {

  

  // Variant class that describes either a number, or index of a symbolic value;
  class Constant {
  public:
    explicit Constant(bool is_symbolic,
		      int num,
		      uint sym_id)    
    : is_symbolic_ {is_symbolic}
    , num_ {num}
    , sym_id_ {sym_id}
    {};
    
    ~Constant()		     	{}

    bool is_symbolic() const	{ return is_symbolic_; }
    int num() const		{ return num_; }
    uint sym_id() const		{ return sym_id_; }
    bool operator<(const Constant& o) const;

  private:
    bool is_symbolic_;
    int num_;
    uint sym_id_;
    friend std::ostream& operator<<(std::ostream& os,
				    const Constant& cons);
  };


  class SCounterConstraint {
  public:
    explicit SCounterConstraint(uint ctr_id,
				Operator op,
				const Constant& cons)
    : ctr_id_ {ctr_id}
    , op_ {op}
    , cons_ {cons}
    {}

    ~SCounterConstraint() 		{}

    uint ctr_id() const 		{ return ctr_id_; }
    Operator op() const 		{ return op_; }
    const Constant& cons() const	{ return cons_; }
    bool operator<(const SCounterConstraint& o) const;

  private:
    uint ctr_id_;
    Operator op_;
    Constant cons_;
    friend std::ostream& operator<<(std::ostream& os,
				    const SCounterConstraint& cc);
  };


  std::ostream& operator<<(std::ostream& os,
			   const std::set<SCounterConstraint>& ccs);
  
  
  class SymbolConstraint {
  public:
    explicit SymbolConstraint(Operator op,
			      const Constant& cons)
    : op_ {op}
    , cons_{cons}
    {};

    ~SymbolConstraint() 		{}

    Operator op() const 		{ return op_; }
    const Constant& cons() const      	{ return cons_; }
    bool operator<(const SymbolConstraint& o) const;

  private:
    Operator op_;
    Constant cons_;
    friend std::ostream& operator<<(std::ostream& os,
				    const SymbolConstraint& sc);
  };


  typedef std::set<SymbolConstraint> SymbolFrm;


  std::ostream& operator<<(std::ostream& os,
			   const SymbolFrm& sc);
  
  // A transition in a CM.
  class CmAction {
  public:
  CmAction(const uint letter_id,
	   const std::set<SCounterConstraint>& ccs,
	   state_t succ,
	   const std::vector<int>& addition,
	   const std::vector<bool>& add_element)
    : letter_id_ {letter_id}
    , ccs_ {ccs}
    , succ_{succ}
    , addition_{addition}
    , add_element_{add_element}
    {}
    
    ~CmAction()					{}

    uint letter_id() const 			{ return letter_id_; }    
    const std::set<SCounterConstraint> counter_constraints() const
    { return ccs_; }
    state_t succ() const 			{ return succ_; }
    const std::vector<int>& addition() const 	{ return addition_; }
    const std::vector<bool>& add_element() const 	{ return add_element_; }
  private:
    uint letter_id_;		// position in the alphabet
    std::set<SCounterConstraint> ccs_;
    state_t succ_;
    std::vector<int> addition_;	// constants to add
    std::vector<bool> add_element_; // add array element value
    
    friend std::ostream& operator<<(std::ostream& os,
				    const CmAction& cma);
  };

  
  // Counter machine with an alphabet of type T.
  template <typename T> class SCM {
  public:
  SCM(uint states_no,
      uint counters_no,
      uint scons_no,
      state_t init_state,
      const std::vector<T>& alphabet,
      const std::vector<std::deque<CmAction>>& tr,
      const std::set<state_t>& acc)
    : states_no_{states_no}
    , counters_no_{counters_no}
    , scons_no_{scons_no}
    , init_state_{init_state}
    , alphabet_{alphabet}
    , tr_{tr}
    , acc_{acc}
    {}

    SCM(CM &&other);
    SCM(const CM& other);
      
    virtual ~SCM() 			       			{ }
    
    uint states_no() const 					{ return states_no_;    }
    uint counters_no() const					{ return counters_no_;  }
    uint sym_constants_no() const 			      	{ return scons_no_; }
    state_t init_state() const		      			{ return init_state_; }
    const std::vector<T>& alphabet() const 			{ return alphabet_;  }
    const std::vector<std::deque<CmAction>>& tr() const 	{ return tr_;  }
    const std::set<state_t>& accepting() const			{ return acc_; }

    void check() const;

  private:
    uint states_no_;
    uint counters_no_;
    uint scons_no_;
    state_t init_state_;
    std::vector<T> alphabet_;
    std::vector<std::deque<CmAction>> tr_;
    std::set<state_t> acc_;

    template <typename U>
      friend std::ostream& operator<<(std::ostream& os,
				      const SCM<U>& cm);
  };

  
  template <typename U>
    std::ostream& operator<<(std::ostream& os,
			     const SCM<U>& cm);
  
  // Computes parallel composition of two CM's defined over the same alphabet.
  SCM<SymbolFrm> parallel(const SCM<SymbolFrm>& cm1,
			  const SCM<SymbolFrm>& cm2,
			  bool doSfSat);


  // Collection of information about a SCM.
  class SCMInfo {
  public:
  SCMInfo(uint tr_size,
	  const std::vector<std::set<uint>>& cmp_const,
	  const std::vector<std::set<uint>>& cmp_symid,
	  const std::vector<bool>& cmp_symid_simple,
	  const std::set<std::set<SCounterConstraint>>& cmp_set,
	  const std::set<std::pair<uint, int>>& update_set)
    : tr_size_ {tr_size}
    , cmp_const_ {cmp_const}
    , cmp_symid_ {cmp_symid}
    , cmp_symid_simple_ {cmp_symid_simple}
    , cmp_set_ {cmp_set}
    , update_set_ {update_set}
    {}
    
    virtual ~SCMInfo()	{}
    
    uint tr_size_;
    std::vector<std::set<uint>> cmp_const_;		// constants in comparison for each counter
    std::vector<std::set<uint>> cmp_symid_;		// symbolic ids in comparison for each counter
    std::vector<bool> cmp_symid_simple_;
    std::set<std::set<SCounterConstraint>> cmp_set_;	// actions constraints
    std::set<std::pair<uint, int>> update_set_;		// counter updates
  };

  
  // TODO move to .cc
  template <typename T>
    SCMInfo getSCMInfo(const SCM<T>& scm);

  
}

#endif 
