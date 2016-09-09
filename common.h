/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef COMMON_H__
#define COMMON_H__

#include <iostream>
#include <vector>
#include <deque>
#include <set>

typedef unsigned int uint;
typedef unsigned long long ullong;
typedef uint state_t;
typedef uint symbol_t;
typedef int counter_t;
typedef std::pair<state_t, std::vector<counter_t>> cm_config;

namespace fold {

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

}

#endif
