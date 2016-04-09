/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <iostream>
#include <fstream>
#include <chrono>
#include <map>
#include <cstring>
#include <string>
#include <sstream>
#include <utility>
#include "common.h"
#include "semptiness.h"
#include "scm.h"
#include "folds.h"
#include "z3++.h"


using std::vector;
using std::deque;
using std::set;
using std::map;
using std::string;
using std::pair;
using std::make_pair;
using std::cout;
using std::cerr;
using std::endl;
using std::flush;
using std::multimap;
using std::chrono::high_resolution_clock;
using std::chrono::duration_cast;
using std::chrono::milliseconds;

using namespace fold;
using namespace z3;

string USAGE_STR =  " formula.smt functions.xml [-model|-nosfsat|-help] \n\nOPTIONS: \n-model		Generate model. \n-nosfsat	Do not use sat check to prune parallel composition.";

int app_no;
// Generate model
bool domodel;
// Prune unsatisfiable symbolic formulas when doing parallel composition
bool dosfsat;

/* Get number of counters and symbolic constants of the fold */
pair<uint, uint> getFoldParams(const string& name){
  vector<string> elems;
  std::stringstream ss(name);
  string item;
  while (getline(ss, item, '_')) {
    elems.push_back(item);
  }

  assert(elems.size() == 3);
  uint p1 = stoi(elems[1]);
  uint p2 = stoi(elems[2]);
  
  return make_pair(p1, p2);
}


/* Transerses the formula and replaces fold applications by fresh
   constants */
expr replaceFolds(const expr& e, solver& s, deque<FoldApplication>& fas){
  assert (e.is_app());

  context& ctx = s.ctx();

  if (e.is_const()) {
    return e;
  }

  func_decl d = e.decl();
  unsigned int sz = e.num_args();
  vector<expr> args;
  for (uint i=0; i<sz; i++){
    expr ep = replaceFolds(e.arg(i), s, fas);
    args.push_back(ep);
  }

  string fname =  d.name().str();
  
  if (fname.size() >= 4 && fname.substr(0,4) == "fold"){
    pair<uint, uint> pr = getFoldParams(fname);
    uint counters_no = pr.first;
    uint sym_const_no = pr.second;
    
    assert(sz == (2 * counters_no + sym_const_no + 2));
	   
    string rel = args[0].decl().name().str();
    string arr = args[1].decl().name().str();

    vector<expr> ins;
    for (uint i=0; i<counters_no; i++){
      expr& in = args[2+i];
      ins.push_back(in);
    }

    vector<expr> outs;
    for (uint i=0; i<counters_no; i++){
      expr& out = args[2+counters_no+i];
      outs.push_back(out);
    }

    vector<expr> scons;
    for (uint i=0; i<sym_const_no; i++){
      expr& scon = args[2+2*counters_no+i];
      scons.push_back(scon);
    }

    string name = "out" + std::to_string(app_no);
    expr sub = ctx.bool_const(name.c_str());
    app_no++;
    FoldApplication fa {rel, arr, sub, ins, outs, scons};
    fas.push_back(fa);
    return sub;
  }

  Z3_ast *ast_args = new Z3_ast[sz];
  for (uint i=0; i<sz; i++){
    ast_args[i] = args[i];
  }

  if (d.name().str() == "and"){
  Z3_ast r = Z3_mk_and(ctx, sz, ast_args);
  delete ast_args;
  return expr {ctx, r};
  }

  Z3_ast r = Z3_mk_app(ctx, d, sz, ast_args);
  delete ast_args;
  return expr {ctx, r};
}


/* Constructs a composite counter machine for the array, and adds a
   formula that checkes their non-emptiness */
void addCmForArrFormula(solver &s,
			vector<SCMEmptinessCheck<SymbolFrm>>& ecs,
			const deque<FoldApplication>& arr_fas,
			const map<string, SCM<SymbolFrm>>& cm_map,
			int arr_no){
  // expressions equal to symbolic constants, and counters values
  map<uint, expr> cm_start_eq, cm_end_eq, cm_symid_eq; 
    
    auto it_fas = arr_fas.begin();
    assert(it_fas != arr_fas.end());
    const FoldApplication& fa = *it_fas;
    
    string rel = fa.rel_;
    auto it_cm = cm_map.find(rel);
    if (it_cm == cm_map.end()){
      cerr << "Error: cannot find relation " << rel << endl;
      assert(false);
    }
    
    SCM<SymbolFrm> comp = it_cm->second;

    const vector<expr>& ins = fa.input_;
    const vector<expr>& outs = fa.output_;
    const vector<expr>& scons = fa.scons_;

    assert(ins.size() == comp.counters_no());

    for (uint k=0; k<ins.size(); k++){
      cm_start_eq.insert(pair<uint, expr>(k, ins[k]));
    }
    for (uint k=0; k<outs.size(); k++){
      cm_end_eq.insert(pair<uint, expr>(k, outs[k]));
    }
    for (uint i=0; i<scons.size(); i++){
      cm_symid_eq.insert(pair<uint, expr>(i, scons[i]));
    }


    for(it_fas++; it_fas!=arr_fas.end(); it_fas++){
      const FoldApplication& fa2 = *it_fas;
      rel = fa2.rel_;
      it_cm = cm_map.find(rel);

      if (it_cm == cm_map.end()){
	cerr << "Error: couldn't find relation " << rel << endl;
	assert(false);
      }

      const SCM<SymbolFrm>& cm = it_cm->second;
      
      int old_k = comp.counters_no();
      int old_symid = comp.sym_constants_no();
      comp = parallel(comp, cm, dosfsat);
      
#ifdef DEBUG
      comp.check();
#endif 
      const vector<expr>& ins2 = fa2.input_;
      assert(ins2.size() == cm.counters_no());
	    
      for (uint k=0; k<ins2.size(); k++){
	cm_start_eq.insert(pair<uint, expr>(old_k+k, ins2[k]));
      }
      
      const vector<expr>& outs2 = fa2.output_;
      for (uint k=0; k<outs2.size(); k++){
	cm_end_eq.insert(pair<uint, expr>(old_k+k, outs2[k]));
      }

      const vector<expr>& scons2 = fa2.scons_;
      for (uint i=0; i<scons2.size(); i++){
	cm_symid_eq.insert(pair<uint, expr>(old_symid+i, scons2[i]));
      }

    }

#ifdef DEBUG
    cout << "Composite CM " << endl;
    cout << comp << endl;
    cout << "Counter mapping:" << endl;
    for (auto itm=cm_start_eq.begin(); itm!=cm_start_eq.end(); itm++){
      cout << "start=" << itm->first << " -> " << itm->second << endl;
    }
    for (auto itm=cm_end_eq.begin(); itm!=cm_end_eq.end(); itm++){
      cout << "end=" << itm->first << " -> " << itm->second << endl;
    }
    for (auto itm=cm_symid_eq.begin(); itm!=cm_symid_eq.end(); itm++){
      cout << "symid=" << itm->first << " -> " << itm->second << endl;
    }
    cout << endl;
#endif

    SCMEmptinessCheck<SymbolFrm> ec {comp};
    string postfix = "^" + std::to_string(arr_no);
    ec.addEmptinessFormula(s, 0, postfix);

    for (auto itm=cm_start_eq.begin(); itm!=cm_start_eq.end(); itm++){
      uint ctr = itm->first;
      expr& e = itm->second;
      s.add(ec.start(ctr) == e);
    }
    for (auto itm=cm_end_eq.begin(); itm!=cm_end_eq.end(); itm++){
      uint ctr = itm->first;
      expr& e = itm->second;
      s.add(ec.end(ctr) == e);
    }
    for (auto itm=cm_symid_eq.begin(); itm!=cm_symid_eq.end(); itm++){
      uint symid = itm->first;
      expr& e = itm->second;
      s.add(ec.scons().at(symid) == e); // TODO make uniform call
    }

    ecs.push_back(ec);
}

/* Add non-emptiness formulas for folds. */
void addCmFormulas(solver &s,
		   vector<SCMEmptinessCheck<SymbolFrm>>& ecs,
		   vector<string>& arr_names,
		   const deque<FoldApplication>& fas,
		   const map<string, SCM<SymbolFrm>>& cm_map){
  set<string> arr_set; 

  for (auto it=fas.begin(); it!=fas.end(); it++){
    string arr = it->arr_;
    arr_set.insert(arr);
  }

  int arr_no = 0;
  for (auto it=arr_set.begin(); it!=arr_set.end(); it++, arr_no++){    
    string arr = *it;
    deque<FoldApplication> arr_fas;

    // find all folds for the array
    for (auto it_fas=fas.begin(); it_fas != fas.end(); it_fas++){
      const FoldApplication& fa = *it_fas;
      string fas_arr = fa.arr_;
      if (arr.compare(fas_arr) == 0){
	arr_fas.push_back(fa);
      }
    }

    arr_names.push_back(arr);
    addCmForArrFormula(s, ecs, arr_fas, cm_map, arr_no);
  }

}


/* Translates "fold" applications into to Pressburger formulas */
void addTranslatedFormula(const expr& fml, solver& s,
			  vector<SCMEmptinessCheck<SymbolFrm>>& ecs,
			  vector<string>& arr_names,
			  map<string, SCM<SymbolFrm>>& cm_map){
  deque<FoldApplication> fas;
  app_no = 0;
  expr e = replaceFolds(fml, s, fas);
#ifdef INFO
  cout << "original formula" << endl <<fml << endl << endl;
  cout << "formula after replacement: " << endl<< e << endl << endl;
#endif 
  addCmFormulas(s, ecs, arr_names, fas, cm_map);
  s.add(e);
}


void flsat(const char *filesmt, const char *filexml){

  context ctx;
  solver s(ctx);
  vector<SCMEmptinessCheck<SymbolFrm>> ecs;
  vector<string> arr_names;
  long int model_time, cons_time, sat_time;

  auto tmr1  = high_resolution_clock::now();
  map<string, SCM<SymbolFrm>> cm_map;
  getCms(filexml, cm_map);
  Z3_ast _fml = Z3_parse_smtlib2_file(ctx, filesmt, 0, 0, 0, 0, 0, 0);
  expr fml(ctx, _fml);  
  addTranslatedFormula(fml, s, ecs, arr_names, cm_map);

#if DEBUG
  cout << s << endl << endl;
#endif
  
  cons_time =
    duration_cast<milliseconds>(high_resolution_clock::now() - tmr1 ).count();
  
  auto tmr2  = high_resolution_clock::now();
  check_result res = s.check();
  sat_time =
    duration_cast<milliseconds>(high_resolution_clock::now() - tmr2 ).count();

    
  if (res){
    cout << "sat" << endl << endl;
    model m = s.get_model();
    
    for (uint i=0; i<ecs.size(); i++){
      string& arr = arr_names[i];
      cout << "Array: " << arr << endl;
      SCMEmptinessCheck<SymbolFrm>& ec = ecs[i];
#ifdef INFO
	ec.printModel(m, cout);
#endif
      // vector<CmAction> lword = ec.wordFromModel(m);     
      // cout << endl << "word: " << endl;
      // for (auto it=lword.begin(); it!=lword.end(); it++){
      // 	const CmAction& cam = *it;
      // 	cout << cam << ", " << endl;
      // }
	
	if (domodel){
	  auto tmr3  = high_resolution_clock::now();
	  vector<int> eword = ec.ewordFromModel(m);
	  model_time =
	    duration_cast<milliseconds>(high_resolution_clock::now() - tmr3 ).count();	  
	  cout << "model: " << eword << endl;
      }

      cout << endl;
    }
  } else {
    cout << "unsat" << endl;
  }

  cout << "Construction time:\t" <<  cons_time << "ms" << endl;
  cout << "Solving time:     \t" <<  sat_time << "ms" << endl;

  if (domodel){
    cout << "Model time:       \t" <<  model_time << "ms" << endl;
  }
}


int main(int argc, char * argv[]) {  
  if (argc < 3) {
    cerr << "USAGE: " << argv[0] << USAGE_STR << endl;
    return 1;
  }

  domodel = false;
  dosfsat = true;

  for (int i = 3; i<argc; i++){
    char* arg = argv[i];
    
    if ((strcmp(arg, "-model") == 0) || (strcmp(arg, "-m") == 0)){
      domodel = true;
    }
    else if (strcmp(arg, "-nosfsat") == 0){
      dosfsat = false;
    }
    else if (strcmp(arg, "-sfsat") == 0){
      dosfsat = true;
    }
    else if ((strcmp(arg, "-help") == 0) || (strcmp(arg, "-h") == 0)){
      cerr << "USAGE: " << argv[0] << USAGE_STR << endl;
      return 0;
    }
    else {
      cerr << "ERROR: unkown option " << arg << endl;
      return 1;
    }

  }

  flsat(argv[1], argv[2]);

  return 0;
}

