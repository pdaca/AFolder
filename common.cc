/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include "common.h"

namespace fold {

  std::ostream& operator<<(std::ostream& os, const std::vector<bool>& v){
    if (v.size() == 0){
      return os << "[]";
    }
    
    os << "[";
    for (uint i=0; i<v.size()-1; i++)
      os << v[i] << ",";

    os << v[v.size() -1] << "]";
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


}
