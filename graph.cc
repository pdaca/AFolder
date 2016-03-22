/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <map>
#include <set>
#include <deque>
#include <cassert>
#include "graph.h"
#include "scm.h"

using std::vector;
using std::map;
using std::set;
using std::deque;
using std::endl;
using std::string;
using std::to_string;
using std::make_pair;
using std::pair;

namespace fold {

  template<typename U>
  std::ostream& operator<<(std::ostream& os, const WeightedLabeledGraph<U>& gr) {
    uint states_no = gr.states_no_;
    const vector<U>& alphabet = gr.alphabet_;
    
    os << "Weighted graph : states_no=" << states_no << endl;
    os << "Alphabet: " << endl;
    for (uint i=0; i<alphabet.size(); i++)
      os << i << " - " << alphabet[i] << endl;
    os << "Tr: " << endl;
    const map<pair<uint, uint>, uint>& weight = gr.weight_;
    const map<pair<uint, uint>, uint>& label = gr.label_;
    
    for (auto it=weight.begin(); it!=weight.end(); it++){
      uint p = it->first.first;
      uint q = it->first.second;
      uint w = it->second;

      auto elem = label.find(it->first);
      uint l = elem == label.end() ? 0 :  elem->second;
	
	if (w > 0){

	  if (l >= 0){
	    os << "s=" << p << ", w=" << w << ", l=" << alphabet[l]
	       << ", s'=" << q << endl;
	  } else {
	    os << "s=" << p << ", w=" << w << ", l= " 
	       << ", s'=" << q << endl;	    
	  }
	  
	}
    }
    return os;
  }
    

  template std::ostream& operator<<(std::ostream& os, const WeightedLabeledGraph<SymbolFrm>& gr);
  template std::ostream& operator<<(std::ostream& os, const WeightedLabeledGraph<CmAction>& gr);


    template<typename T>
    deque<uint> getEulerianPath(WeightedLabeledGraph<T>& graph, uint start){ 
    uint states_no = graph.states_no_;
    map<pair<uint,uint>, uint>& weight = graph.weight_;
    vector<uint> outdegree (states_no);
    vector<uint> indegree (states_no);
    deque<uint> path, stack;

    for (uint i=0; i<states_no; i++){
      for (uint j=0; j<states_no; j++){
	pair<uint, uint> pr {i, j};
	auto elem = weight.find(pr);
	if (elem == weight.end())
	  continue;

	uint w = elem->second;
	outdegree[i] += w;
	indegree[j] += w;
      }
    }

    // check that the graph has an eulerian path
    int no_even = 0;
    for (uint i=0; i<states_no; i++){
      int diff = outdegree[i] - indegree[i];
      assert(diff >= -1 && diff <= 1);
      if (diff != 0)
	no_even++;
    }
    assert(no_even == 0 || no_even == 2);

    uint s = start;
    stack.push_back(s);

    while(!stack.empty() || outdegree[s]>0){
      if (outdegree[s] == 0){
	path.push_front(s);
	s = stack.back();
	stack.pop_back();
      } else {
	stack.push_back(s);

	uint j=0;

	pair<uint, uint> pr;
	uint w = 0;
	while(j<states_no) {
	  pr = make_pair(s,j);
	  auto elem = weight.find(pr);
	  if (elem != weight.end() && elem->second > 0){
	    w = elem->second;
	    break;
	  }
	  j++;	  	  
	}
	
	// while(weight[s][j] == 0 && j<states_no)
	//   j++;

	if (j==states_no)
	  assert(false);
	
	weight[pr] = w-1;
	outdegree[s]--;
	s = j;
      }
    }
    return path;
  }

  template     deque<uint> getEulerianPath(WeightedLabeledGraph<CmAction>& graph, uint start);


}
