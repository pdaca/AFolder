/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include "common.h"

using namespace z3;
using std::invalid_argument;

namespace fold {

  std::ostream& operator<<(std::ostream& os, Operator op){
    switch (op){
    case EQ :
      os << "=";
      break;
      
    case GT :
      os << ">";
      break;
      
    case LT :
      os << "<";
      break;
      
    case LEQ :
      os << "<=";
      break;
      
      
    case GEQ :
      os << ">=";
      break;
      
    case NEQ :
      os << "!=";
      break;
      
    default :
      os << "?";
    }
    
    return os;
  }

  
  std::ostream& operator<<(std::ostream& os, const std::vector<bool>& v){
    if (v.size() == 0){
      return os << "[]";
    }
    
    os << "[";
    for (uint i=0; i<v.size(); i++)
      if (v[i])
	os << i << ",";

    os << "]";
    return os;
  }


  std::ostream& operator<<(std::ostream& os, const std::vector<int>& v){
    if (v.size() == 0){
      return os << "[]";
    }
    
    os << "[";
    for (uint i=0; i<v.size()-1; i++)
      os << v[i] << ",";

    os << v[v.size() -1] << "]";
    return os;
  }


  std::ostream& operator<<(std::ostream& os, const std::set<int>& v){
    if (v.empty()){
      return os << "[]";
    }
    
    os << "[";
    auto it=v.begin();
    unsigned i=0;
    for (; i<v.size()-1; it++, i++)
      os << *it << ",";

    return os  << *it << "]";
  }

  
  std::ostream& operator<<(std::ostream& os, const std::set<uint>& v){
    if (v.empty()){
      return os << "[]";
    }
    
    os << "[";
    auto it=v.begin();
    unsigned i=0;
    for (; i<v.size()-1; it++, i++)
      os << *it << ",";

    return os  << *it << "]";
  }

  std::ostream& operator<<(std::ostream& os, const std::deque<state_t>& v){
    if (v.size() == 0){
      return os << "[]";
    }
    
    os << "[";
    uint i=0;
    for (auto it=v.begin(); i<v.size()-1; it++, i++)
      os << *it << ",";

    os << v.back() << "]";
    return os;
  }



  std::ostream& operator<<(std::ostream& os, const std::vector<uint>& v){
    if (v.size() == 0){
      return os << "[]";
    }

    os << "[";
    for (uint i=0; i<v.size()-1; i++)
      os << v[i] << ",";

    os << v[v.size() -1] << "]";
    return os;
  }



  
  std::ostream& operator<<(std::ostream& os, const std::deque<std::string>& d){
    for (auto it=d.cbegin(); it!=d.cend()-1; it++)
      os << *it << " ";

    return os << d.back();
  }


  std::ostream& operator<<(std::ostream& os, const std::vector<std::string>& v){
    if (v.size() == 0){
      return os << "[]";
    }

    os << "[";
    for (uint i=0; i<v.size()-1; i++)
      os << v[i] << ",";

    os << v[v.size() -1] << "]";
    return os;
  }

  std::ostream& operator<<(std::ostream& os, const cm_config& cnf) {
    os << "s=" << cnf.first << "," << cnf.second;
    return os;
  }


  std::ostream& operator<<(std::ostream& os, const std::deque<cm_config>& d){
    if (d.empty()){
      return os << "[]";
    }
    
    os << "[";
    for (auto it=d.cbegin(); it!=d.cend()-1; it++)
      os << *it << ",";

    os << d.back() << "]";
    return os;
  }

  
  uint  getZ3UintValue(const model& m, const expr& var){
    expr eval = m.eval(var); 
    uint val = 0;
    Z3_bool ok = Z3_get_numeral_uint(eval.ctx(), eval, &val);

    if (!ok){
      throw invalid_argument("Cannot get value for a variable");
    }

    return val;
  }

  int  getZ3IntValue(const model& m, const expr& var){
    expr eval = m.eval(var); 
    int val = 0;
    Z3_bool ok = Z3_get_numeral_int(eval.ctx(), eval, &val);

    if (!ok){
      throw invalid_argument("Cannot get value for a variable");
    }

    return val;
  }


}
