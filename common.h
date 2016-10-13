/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef COMMON_H__
#define COMMON_H__

#include <iostream>
#include <vector>
#include <deque>
#include <stdexcept>
#include <set>
#include "z3++.h"

typedef unsigned int uint;
typedef unsigned long long ullong;
typedef uint state_t;
typedef uint symbol_t;
typedef int counter_t;
typedef std::pair<state_t, std::vector<counter_t>> cm_config;

namespace fold {

  enum Operator {EQ, NEQ, LT, GEQ, GT,LEQ };

  std::ostream& operator<<(std::ostream& os, Operator op);
  std::ostream& operator<<(std::ostream& os, const std::vector<bool>& v);
  std::ostream& operator<<(std::ostream& os, const std::vector<int>& v);
  std::ostream& operator<<(std::ostream& os, const std::set<int>& v);
  std::ostream& operator<<(std::ostream& os, const std::set<uint>& v);
  std::ostream& operator<<(std::ostream& os, const std::deque<state_t>& v);
  std::ostream& operator<<(std::ostream& os, const std::vector<uint>& v);
  std::ostream& operator<<(std::ostream& os, const std::deque<std::string>& d);
  std::ostream& operator<<(std::ostream& os, const std::vector<std::string>& v);
  std::ostream& operator<<(std::ostream& os, const cm_config& cnf);
  std::ostream& operator<<(std::ostream& os, const std::deque<cm_config>& d);

  // get variable valuation from a model
  uint getZ3UintValue(const z3::model& m, const z3::expr& var);
  int getZ3IntValue(const z3::model& m, const z3::expr& var);


}

#endif
