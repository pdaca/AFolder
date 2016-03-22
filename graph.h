/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#ifndef GRAPH_H__
#define GRAPH_H__

#include <deque>
#include <vector>
#include "common.h"

namespace fold {

  template<typename T>
    class WeightedLabeledGraph {
  public:
    
      WeightedLabeledGraph()
    : states_no_{0}
    , weight_{}
    , label_{}
    , alphabet_{}
    {};

  WeightedLabeledGraph(uint states_no,
		       const std::map<std::pair<uint,uint>, uint>& weight,
		       const std::map<std::pair<uint,uint>, uint>& label,
		       const std::vector<T>& alphabet_symbols)
    : states_no_{states_no}
    , weight_{weight}
    , label_{label}
    , alphabet_{alphabet_symbols}
    {}

  WeightedLabeledGraph(const WeightedLabeledGraph& other)
    : states_no_ {other.states_no_}
    , weight_  { other.weight_ }
    , label_   { other.label_ }
    , alphabet_ { other.alphabet_ }
    {}


  WeightedLabeledGraph(const WeightedLabeledGraph&& other)
    : states_no_{ other.states_no_ }
    , weight_  { move(other.weight_) }
    , label_   { move(other.label_) }
    , alphabet_ { move(other.alphabet_) }
    {}
    
    virtual ~WeightedLabeledGraph()		{}

    uint states_no_;
    std::map<std::pair<uint,uint>, uint> weight_;
    std::map<std::pair<uint,uint>, uint> label_;
    std::vector<T> alphabet_;

    template <typename U>
    friend std::ostream& operator<<(std::ostream& os, const WeightedLabeledGraph<U>& gr);
  };

  template<typename T>
    std::deque<uint> getEulerianPath(WeightedLabeledGraph<T>& graph, uint start);

}

#endif

