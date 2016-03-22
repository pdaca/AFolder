#include <iostream>
#include <utility>
#include <cassert>
#include "folds.h"
#include "tinyxml/tinyxml.h"

using std::cout;
using std::cerr;
using std::endl;
using std::vector;
using std::map;
using std::set;
using std::deque;
using std::pair;
using std::string;


namespace fold {

  std::ostream& operator<<(std::ostream& os, const FoldApplication& fa) {
    os << "FoldApplication "
       << "rel=" << fa.rel_ << ", arr=" << fa.arr_
       << ", sub=" << fa.sub_ << ", input=[";
    for (auto it=fa.input_.begin(); it!=fa.input_.end(); it++){
      os << *it << ",";
    }
    os << "], output=[";
    for (auto it=fa.output_.begin(); it!=fa.output_.end(); it++){
      os << *it << ",";
    }
    os << "], scons=[";
    for (auto it=fa.scons_.begin(); it!=fa.scons_.end(); it++){
      os << *it << ",";
    }
    os << "]" << std::endl;
    return os;
  }

  
  Operator getOperator(TiXmlAttribute* att){
    assert(att);
    Operator op;   

    if (strcmp("EQ", att->Value()) == 0){
      op = Operator::EQ;
    }
    else if (strcmp("GT", att->Value()) == 0){
      op = Operator::GT;
    }
    else if (strcmp("LT", att->Value()) == 0){
      op = Operator::LT;
    }
    else if (strcmp("GEQ", att->Value()) == 0){
      op = Operator::GEQ;
    }
    else if (strcmp("LEQ", att->Value()) == 0){
      op = Operator::LEQ;
    }
    else if (strcmp("NEQ", att->Value()) == 0){
      op = Operator::NEQ;
    }
    else {
      assert(false);
    }

    return op;
  }
  

  SCounterConstraint getSCounterConstraint(TiXmlNode *node){
    assert(node);
    TiXmlAttribute* att = node->ToElement()->FirstAttribute();

    bool numeric_given = false;
    bool symbolic_given = false;
    bool relation_given = false;
    bool ctrid_given = false;
    Operator op = Operator::EQ;
    int num;
    int sym_id;
    int ctr_id;

    while (att) {
      if (COUNTER_ID_ATT.compare(att->Name()) == 0){
	if (att->QueryIntValue(&ctr_id) != TIXML_SUCCESS)
	  assert(false);

	ctrid_given = true;
      }
      else if (RELATION_ATT.compare(att->Name()) == 0){
	op = getOperator(att);
	relation_given = true;
      }
      else if (NUMERIC_CONS_ATT.compare(att->Name()) == 0){
	if (att->QueryIntValue(&num) != TIXML_SUCCESS)
	  assert(false);

	numeric_given = true;
      }
      else if (SYMBOLIC_CONS_ATT.compare(att->Name()) == 0){
	if (att->QueryIntValue(&sym_id) != TIXML_SUCCESS){
	  cerr << att->Name() << endl;
	  assert(false);
	}

	symbolic_given = true;
      }
      else {
	cerr << "Error: unregonized attribute " << att->Name() << endl;
	assert(false);
      }
      
      att = att->Next();
    }

    assert(ctrid_given && relation_given && (numeric_given || symbolic_given)
	   && (!numeric_given || !symbolic_given));
    assert(ctr_id >= 1);

    assert(!symbolic_given || (sym_id >= 1));
    Constant cons {symbolic_given, num, (uint) sym_id-1};

    SCounterConstraint cs {(uint) (ctr_id-1), op, cons};
    return cs;
  }


  SymbolConstraint getSymbolConstraint(TiXmlNode *node){
    TiXmlAttribute* att = node->ToElement()->FirstAttribute();

    bool numeric_given = false;
    bool symbolic_given = false;
    bool relation_given = false;
    Operator op;
    int num;
    int sym_id;

    while (att) {

      if (RELATION_ATT.compare(att->Name()) == 0){
	op = getOperator(att);
	relation_given = true;
      }
      else if (NUMERIC_CONS_ATT.compare(att->Name()) == 0){
	if (att->QueryIntValue(&num) != TIXML_SUCCESS)
	  assert(false);

	numeric_given = true;
      }
      else if (SYMBOLIC_CONS_ATT.compare(att->Name()) == 0){
	if (att->QueryIntValue(&sym_id) != TIXML_SUCCESS)
	  assert(false);

	symbolic_given = true;
      }
      else {
	assert(false);
      }
      
      att = att->Next();
    }

    assert(relation_given && (numeric_given || symbolic_given)
	   && (!numeric_given || !symbolic_given));

    assert(!symbolic_given || (sym_id >= 1));
    Constant cons {symbolic_given, num, (uint) sym_id-1};
    
    SymbolConstraint sc {op, cons};
    return sc;
  }


  pair<uint, int> getUpdatePair(TiXmlNode *node){
        TiXmlAttribute* att = node->ToElement()->FirstAttribute();

    bool numeric_given = false;
    bool ctrid_given = false;
    int num;
    int ctr_id;

    while (att) {

      if (COUNTER_ID_ATT.compare(att->Name()) == 0){
	if (att->QueryIntValue(&ctr_id) != TIXML_SUCCESS)
	  assert(false);

	ctrid_given = true;
      }
      else if (NUMERIC_CONS_ATT.compare(att->Name()) == 0){
	if (att->QueryIntValue(&num) != TIXML_SUCCESS)
	  assert(false);

	numeric_given = true;
      }
      else {
	assert(false);
      }
      
      att = att->Next();
    }

    assert(ctrid_given && numeric_given);
    assert(ctr_id >= 1);

    pair<uint, int> pr= std::make_pair((uint) ctr_id-1, num);
    return pr;
  }

  
  void addCmAction(TiXmlNode *node,
		   uint counters_no,
		   int mode,
		   deque<CmAction>& actions,
		   map<SymbolFrm, uint>& letter_map){
    set<SCounterConstraint> ccs;
    set<SymbolConstraint> scs;
    vector<int> addition (counters_no);
    int succ = mode;

    for (TiXmlNode* child = node->FirstChild(); child != NULL; child = child->NextSibling()){
      if (CGUARD_TAG.compare(child->Value()) == 0){	
	SCounterConstraint cc = getSCounterConstraint(child);
	ccs.insert(cc);
      }
      else if (SGUARD_TAG.compare(child->Value()) == 0){
	SymbolConstraint sc = getSymbolConstraint(child);
	scs.insert(sc);
      }
      else if (CTR_UPDATE_TAG.compare(child->Value()) == 0){
	pair<uint, int> up = getUpdatePair(child);
	addition[up.first] = up.second;
      }
      else if (MODE_UPDATE_TAG.compare(child->Value()) == 0){
	TiXmlAttribute* att = child->ToElement()->FirstAttribute();

	// get successor mode
	while (att) {
	  if (MODE_ID_ATT.compare(att->Name()) == 0){
	    if (att->QueryIntValue(&succ) != TIXML_SUCCESS)
	      assert(false);
	  }
	  else {
	    assert(false);
	  }
      
	  att = att->Next();
	}
      }
      else {
	cerr << "Error unkown tag " << child->Value() << endl;
	assert(false);
      }
    }

    assert (succ >= 1);

    uint letter_id = 0;
    auto elem = letter_map.find(scs);
    if (elem == letter_map.end()){
      letter_id = letter_map.size();
      letter_map.insert(make_pair(scs, letter_id));
    } else {
      letter_id = elem->second;
    }

    CmAction cma {letter_id, ccs, (uint) succ-1, addition};
    actions.push_back(cma);
  }


  /* Extract the counter machine for the XML element */
  void addCm(TiXmlElement *elem, map<string, SCM<SymbolFrm>>& cm_map) {
    bool name_given = false;
    bool counters_given = false;
    string name;
    int counters_no;
    int sconst = 0;
    int modes = 1;
  
    TiXmlAttribute* att2 = elem->FirstAttribute();
    while (att2){
      if (FUNCTION_NAME_ATT.compare(att2->Name()) == 0){
	name_given = true;
	name = att2->Value();
      }
      else if (FUNCTION_COUNTERS_ATT.compare(att2->Name()) == 0) {
	if (att2->QueryIntValue(&counters_no)!=TIXML_SUCCESS)
	  assert(false);

	counters_given = true;
      }
      else if (FUNCTION_SCONST_ATT.compare(att2->Name()) == 0) {
	if (att2->QueryIntValue(&sconst)!=TIXML_SUCCESS)
	  assert(false);
      }
      else if (FUNCTION_MODES_ATT.compare(att2->Name()) == 0) {
	if (att2->QueryIntValue(&modes)!=TIXML_SUCCESS)
	  assert(false);
      }
      else {
	// TODO unkown attibute
	cout << att2->Name() << endl;
	assert(false);
      }
    
      att2 = att2->Next();
    }

    assert(name_given && counters_given && counters_no >= 0 && sconst >= 0 && modes >= 1);
    map<SymbolFrm, uint> letter_map;
    vector<deque<CmAction>> tr (modes);

    for (TiXmlNode* child = elem->FirstChild(); child != NULL; child = child->NextSibling()){
      if (CASE_TAG.compare(child->Value()) == 0){

	// find which mode
	int mode = 1;
	TiXmlAttribute* att = child->ToElement()->FirstAttribute();
	while (att){
	  if (MODE_ID_ATT.compare(att->Name()) == 0){
	    if (att->QueryIntValue(&mode)!=TIXML_SUCCESS)
	      assert(false);
	  }
	  else {
	    // TODO unkown attibute
	    assert(false);
	  }
       
	  att = att->Next();
	}
	assert(mode >= 1 && modes <= modes);

	addCmAction(child, counters_no, mode, tr[mode-1], letter_map);
      }
    }

    vector<SymbolFrm> alphabet (letter_map.size());
    uint i=0;
    for (auto it=letter_map.begin(); it!=letter_map.end(); it++, i++){
      alphabet[it->second] = it->first;
    }

    // add states are accepting
    set<state_t> acc;;
    for (uint j=0; j<(uint)modes; j++){
      acc.insert(j);
    }
    SCM<SymbolFrm> cm {(uint) modes, (uint)counters_no, (uint) sconst, 0, alphabet, tr, acc};
#ifdef INFO
    cm.check();
#endif
    cm_map.insert(std::make_pair(name, cm));
  }


  void getCms(const char* file, std::map<string, SCM<SymbolFrm>>& cm_map){
    TiXmlDocument doc(file);
    bool ok = doc.LoadFile();
    if (!ok){
      cerr << "Failed to parse file " << file << endl;
      return;
      // TODO throw an exception
    }

    for (TiXmlNode* child = doc.FirstChild(); child != NULL; child = child->NextSibling()){
      if (FUNCTION_TAG.compare(child->Value()) == 0){
	addCm(child->ToElement(), cm_map);
      }
    }
    
    
#ifdef DEBUG
    cout << "Read from the XML file:" << endl;
    for (auto it=cm_map.begin(); it!=cm_map.end(); it++){
      cout << "name=" << it->first << endl;
      cout << it->second << endl;      
    }
    cout << endl;
#endif
  }



}
