/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef FOLDS_H__
#define FOLDS_H__

#include <vector>
#include <map>
#include "scm.h"
#include "z3++.h"


namespace fold {


  const std::string FUNCTION_TAG = "function";
  const std::string CASE_TAG = "case";
  const std::string SGUARD_TAG = "symbol_constraint";
  const std::string CGUARD_TAG = "ctr_constraint";
  const std::string CTR_UPDATE_TAG = "ctr_update";
  const std::string MODE_UPDATE_TAG = "mode_update";
  const std::string FUNCTION_NAME_ATT = "name";
  const std::string FUNCTION_COUNTERS_ATT = "counters";
  const std::string FUNCTION_SCONST_ATT = "symbolic";
  const std::string FUNCTION_MODES_ATT = "modes";
  const std::string RELATION_ATT = "relation";
  const std::string COUNTER_ID_ATT = "counter";
  const std::string MODE_ID_ATT = "mode";
  const std::string NUMERIC_CONS_ATT = "numeric";
  const std::string SYMBOLIC_CONS_ATT = "symbolic";

  // Describes fold application in a logic formula.
  class FoldApplication {
  public:
    FoldApplication (const std::string rel,
		     const std::string arr,
		     const z3::expr& sub,
		     const std::vector<z3::expr>& input,
		     const std::vector<z3::expr>& output,
		     const std::vector<z3::expr>& scons)
      : rel_ {rel}
    , arr_ {arr}
    , sub_{sub}
    , input_ {input}
    , output_ {output}
    , scons_ {scons}
    {}
    
    ~FoldApplication()		{};
    
    const std::string rel_;
    const std::string arr_;
    const z3::expr sub_;
    const std::vector<z3::expr> input_;
    const std::vector<z3::expr> output_;
    const std::vector<z3::expr> scons_;

    friend std::ostream& operator<<(std::ostream& os, const FoldApplication& fa);
  };


  /* Parse the XML file to get description of fold functions. Then
     translate the functions into counter machines. */
  void getCms(const char* file, std::map<std::string, SCM<SymbolFrm>>& cm_map);


}


#endif
