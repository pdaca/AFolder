/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef PARIKH_H__
#define PARIKH_H__

#include <vector>
#include <map>
#include "common.h"
#include "automata.h"
#include "z3++.h"

namespace fold {

/* Adds a Pressburger constraints that binds variables in "aparikh"
    to Parikh images of symbols. */
  template <typename T>
void addParikhFormula(z3::solver &s,
		      NFA<T>& nfa,
		      const std::vector<z3::expr>& aparikh,
		      std::string postfix,
		      // container for flow variables
		      std::map<std::pair<state_t, NfaAction>, z3::expr>& flow_map);

}

#endif
