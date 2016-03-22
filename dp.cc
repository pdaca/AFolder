/*
  Copyright (c) 2016 Przemyslaw Daca
  See the file LICENSE for copying permission.
*/
#include <iostream>
#include <chrono>

#include "automata.h"
#include "pda.h"
#include "cm.h"
#include "emptiness.h"


using std::cout;
using std::endl;
using namespace std::chrono;

using z3::context;
using z3::solver;
using namespace fold;


int test1();
int test2();
void test_pda();
void test_codespan();
void test_isheaderline();
void test_nfa_minimization();

int main (int argc, char *argv[]) {
  //test1();
  //test2();
  //test_codespan();
  //test_pda();
  //test_nfa_minimization();
  test_isheaderline();

  
}

// for the path
// i=0
// data[i] == '='
// for (i = 1; i < size && data[i] == '='; i++);
// while (i < size && data[i] == ' ') i++;
// i<size
// data[i] == '\n'


void test_isheaderline(){

  context c;
  solver s(c);

  vector<string> alpha {"=", "s", "\\n", "X", "#"}; // =, space, newline, other character, end of string
  vector<string> sample {"=", "=", "s", "s", "\\n", "#"};

    // cm for specifing length
  CMBuilder builderl {2, 1, alpha};
  builderl.setInitState(0);
  builderl.addAccepting(1);
  builderl.addMove(0, 0, "=", vector<int>{1});
  builderl.addMove(0, 0, "s", vector<int>{1});
  builderl.addMove(0, 0, "\\n", vector<int>{1});
  builderl.addMove(0, 0, "X", vector<int>{1});
  builderl.addMove(0, 1, "#", vector<int>{0});
  builderl.addSelfloop(1);
  CM cml = builderl.build();

  assert(cml.check());
  cout << cml << endl;

  // data[i] == '=' (c0 is the value of i)
  CMBuilder builder0 {2, 1, alpha};
  CounterConstraint cc0 {0, EQ, 0};
  CounterConstraint cc0p {0, GT, 0};
  builder0.setInitState(0);
  builder0.addAccepting(1);
  builder0.addMove(0, 0, "=", cc0p, vector<int>{-1});
  builder0.addMove(0, 0, "s", cc0p, vector<int>{-1});
  builder0.addMove(0, 0, "\\n", cc0p, vector<int>{-1});
  builder0.addMove(0, 0, "X", cc0p, vector<int>{-1});
  builder0.addMove(0, 1, "=", cc0, vector<int>{0});
  builder0.addSelfloop(1);
  const CM cm0 = builder0.build();

  assert(cm0.check());
  cout << cm0 << endl;
  cout << cm0.run(sample, vector<counter_t>{1}) << endl;

  // for (i = 1; i < size && data[i] == '='; i++);
  CMBuilder builder1 {3, 1, alpha};
  builder1.setInitState(0);
  builder1.addAccepting(2);
  builder1.addMove(0, 1, "=", vector<int>{1});
  builder1.addMove(0, 1, "s", vector<int>{1});
  builder1.addMove(0, 1, "\\n", vector<int>{1});
  builder1.addMove(0, 1, "X", vector<int>{1});
  builder1.addMove(1, 1, "=", vector<int>{1});
  builder1.addMove(1, 2, "s", vector<int>{0});
  builder1.addMove(1, 2, "\\n", vector<int>{0});
  builder1.addMove(1, 2, "X", vector<int>{0});
  builder1.addMove(1, 2, "#", vector<int>{0});
  builder1.addSelfloop(2);
  const CM cm1 = builder1.build();

  assert(cm1.check());
  cout << cm1 << endl;

  deque<cm_config> run1 = cm1.run(sample, vector<counter_t> {0});
  cout << run1 << endl;

  // while (i < size && data[i] == ' ') i++; (c0 is the output val, c1 is the initialization)
  CMBuilder builder2 {3, 2, alpha};
  CounterConstraint cc1 {1, EQ, 1};
  CounterConstraint cc2 {1, GT, 1};
  builder2.setInitState(0);
  builder2.addAccepting(2);
  builder2.addMove(0, 0, "=", cc2, vector<int>{1,-1});
  builder2.addMove(0, 0, "s", cc2, vector<int>{1,-1});
  builder2.addMove(0, 0, "\\n", cc2, vector<int>{1,-1});
  builder2.addMove(0, 0, "X", cc2, vector<int>{1,-1});
  builder2.addMove(0, 1, "=", cc1, vector<int>{1,-1});
  builder2.addMove(0, 1, "s", cc1, vector<int>{1,-1});
  builder2.addMove(0, 1, "\\n", cc1, vector<int>{1,-1});
  builder2.addMove(0, 1, "X", cc1, vector<int>{1,-1});
  builder2.addMove(1, 1, "s", vector<int>{1,0});
  builder2.addMove(1, 2, "\\n", vector<int>{0,0});
  builder2.addMove(1, 2, "X", vector<int>{0,0});
  builder2.addMove(1, 2, "#", vector<int>{0,0});
  builder2.addSelfloop(2);
  const CM cm2 = builder2.build();

  cout << cm2 << endl;
  assert(cm2.check());
  deque<cm_config> run2 = cm2.run(sample, vector<counter_t> {0,2});
  cout << run2 << endl;  

  // data[i] == '\n' (c0 is the value of i)
  CMBuilder builder3 {2, 1, alpha};
  builder3.setInitState(0);
  builder3.addAccepting(1);
  builder3.addMove(0, 0, "=", cc0p, vector<int>{-1});
  builder3.addMove(0, 0, "s", cc0p, vector<int>{-1});
  builder3.addMove(0, 0, "\\n", cc0p, vector<int>{-1});
  builder3.addMove(0, 0, "X", cc0p, vector<int>{-1});
  builder3.addMove(0, 1, "\\n", cc0, vector<int>{0});
  builder3.addSelfloop(1);
  const CM cm3 = builder3.build();

  assert(cm3.check());
  cout << cm3 << endl;
  cout << cm3.run(sample, vector<counter_t>{4}) << endl;

  // take the big product cml || cm0 || .. || cm3
  // c0 - length, c1 - index of first check, c2 - val of loop 1.,
  // c3 - output of loop 2., c4 - init of loop 2.,
  // c5 - index of second check
  CM cml0 = CMParallel::parallel(cml, cm0);
  assert(cml0.check());
  CM cml1 = CMParallel::parallel(cml0, cm1);
  assert(cml1.check());
  CM cml2 = CMParallel::parallel(cml1, cm2);
  assert(cml2.check());
  CM cml3 = CMParallel::parallel(cml2, cm3);
  assert(cml3.check());

  cout << cml3 << endl;

  deque<deque<cm_config>> runs = cml3.runAll(sample, vector<counter_t>{0, 1, 0, 0, 2, 4});
  for (auto it=runs.begin(); it!=runs.end(); it++)
    cout << *it << endl;
  cout << endl;

  HagueEmptinessCheck ec {};
  ec.addEmptinessFormula(c, s, cml3, 0, "");
  // init counting to zero
  s.add(ec.start(0) == 0); 
  s.add(ec.start(2) == 0);
  s.add(ec.start(3) == 0);
  
  const expr& size = ec.end(0);
  const expr& check1 = ec.start(1);
  const expr& l1val = ec.end(2);
  const expr& l2init = ec.start(4);
  const expr& l2val = ec.end(3);
  const expr& check2 = ec.start(5);

  s.add(check1 == 0); // first check at i=0
  s.add(l1val == l2init); // result of loop 1 is the input to loop 2
  s.add(l2val == check2); // at second check is at the result of loop 2
  s.add(l2val < size);     // i<size
  s.add(l1val == 10);
  s.add(l2val == 20);
  s.add(size == 21);

  //  cout << s << endl;

  auto t1  = high_resolution_clock::now();
  check_result res = s.check();
  auto t2  = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>( t2 - t1 ).count();
  cout << "Solving time: " << duration << "ms" << endl;
    
  if (res){
    cout << "sat" << endl;
    model m = s.get_model();
    ec.printModel(m, cout);
    vector<string> lword = ec.wordFromModel(m, cml3);
    cout << endl << "word: " << lword << endl;
  } else {
    cout << "unsat" << endl;
  }




  
}


void test_codespan(){
  context c;
  solver s(c);


  vector<string> alpha {"s", "`", "X", "#"};

  // cm for specifing length
  CMBuilder builderl {2, 1, alpha};
  builderl.setInitState(0);
  builderl.addAccepting(1);
  builderl.addMove(0, 0, "`", vector<int>{1});
  builderl.addMove(0, 0, "s", vector<int>{1});
  builderl.addMove(0, 0, "X", vector<int>{1});
  builderl.addMove(0, 1, "#", vector<int>{0});
  CM cml = builderl.build();

  cout << "cml" << endl;
  cout << cml << endl;

  // HagueEmptinessCheck empty_l;
  // empty_l.addEmptinessFormula(c, s, cml, 0, "^cml");
  // const expr& end01_l = empty_l.endc()[0][1];
  // s.add(end01_l == 10);

  // first while loop
  CMBuilder builder1 {2, 1, alpha};
  builder1.setInitState(0);
  builder1.addAccepting(1);
  builder1.addMove(0, 0, "`", vector<int>{1});
  builder1.addMove(0, 1, "s", vector<int>{0});
  builder1.addMove(0, 1, "X", vector<int>{0});
  builder1.addMove(0, 1, "#", vector<int>{0});
  CM cm1 = builder1.build();

  cout << "cm1" << endl;
  cout << cm1 << endl;

  // CM cm1l = CMParallel::parallel(cml, cm1);
  // cout << "cm1l" << endl;
  // cout << cm1l << endl;
  // HagueEmptinessCheck empty_1l;
  // empty_1l.addEmptinessFormula(c, s, cm1l, 0, "^cm1");
  // s.add(empty_1l.start(0) == 0);
  // s.add(empty_1l.start(1) == 0);
  // // add constraint that length and nb is fourty
  // s.add(empty_1l.end(0) == 40);
  // s.add(empty_1l.end(1) == 40);

  // if (s.check()){
  //   cout << "sat" << endl;
  //   model m = s.get_model();
  //   empty_1l.printModel(m, cout);
  //   deque<string> lword = empty_1l.wordFromModel(m, cm1);
  //   cout << endl << "word: " << lword << endl;
  // } else {
  //   cout << "unsat" << endl;
  //   assert(0);
  // }

}


void test_pda(){

  vector<string> alphabet_symbols {"0","1"};
  vector<string> stack_symbols {"Z","A"};

  vector<vector<vector<PDAtransition>>> tr (3, vector<vector<PDAtransition>>(3));
  PDAtransition t1 {0, 0, vector<uint>{1,0}};
  tr[0][0].push_back(t1);
  PDAtransition t2 {0, 1, vector<uint>{1,1}};
  tr[0][0].push_back(t2);
  PDAtransition t3 {1, 0, vector<uint>{0}};
  tr[0][2].push_back(t3);
  PDAtransition t4 {1, 1, vector<uint>{0}};
  tr[0][2].push_back(t4);
  PDAtransition t5 {1, 1, vector<uint>{}};
  tr[1][1].push_back(t5);
  PDAtransition t6 {2, 0, vector<uint>{0}};
  tr[1][3].push_back(t6);
  
  PDA pda(3, 0, alphabet_symbols, stack_symbols, tr, set<state_t>{2});
  cout << pda << endl;
  assert(pda.check());

}



// Unit test 1
// Machine that sums "X"s, but at most two between any "|" delimiters
int test1(){
  vector<string> alphabet_symbols {"X", "|", "#"};

  CMBuilder builder {4, 2, alphabet_symbols};

  builder.setInitState(0);
  builder.addAccepting(3);
  builder.addMove(0,1,"X", vector<int>{1,1});
  builder.addMove(0,0,"|", vector<int>{0,1});
  builder.addMove(0,3,"#", vector<int>{0,0});
  builder.addMove(1,2,"X", vector<int>{1,1});
  builder.addMove(1,0,"|", vector<int>{0,1});
  builder.addMove(1,3,"#", vector<int>{0,0});
  builder.addMove(2,2,"X", vector<int>{0,1});
  builder.addMove(2,0,"|", vector<int>{0,1});
  builder.addMove(2,3,"#", vector<int>{0,1});
  
  CM sum12 = builder.build();
  assert(sum12.check());
  cout << sum12 << endl;

  vector<symbol_t> word = {0,0,1,0,1,0,0,0,2};
  deque<cm_config> dcm = sum12.run(word, vector<counter_t> {0,0});
  cout << "Config after word " << word << endl;
  cout << dcm << endl;
  const cm_config& last_config = dcm.back();
  assert(last_config.first == 3);

  context c;
  solver s(c);

  HagueEmptinessCheck empty_check;

  // add satifiable constraints
  empty_check.addEmptinessFormula(c, s, sum12, 0, "^t");
  s.add(empty_check.start(0) == 0);
  s.add(empty_check.start(1) == 0);
  
  s.add(empty_check.end(0) == 6);
  if (s.check()){
    cout << "sat" << endl;
    cout << "Model:" << endl;

      model m = s.get_model();
      // for (unsigned i = 0; i < m.size(); i++) {
      // 	func_decl v = m[i];
      // 	// this problem contains only constants
      // 	assert(v.arity() == 0);
      // 	std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
      // }
      empty_check.printModel(m, cout);
      vector<string> lword = empty_check.wordFromModel(m, sum12);

      cout << endl << "word: " << endl;
      for (auto it=lword.begin(); it!=lword.end(); it++){
	cout << *it << " " ;
      }
      cout << endl;
  } else {
    cout << "unsat" << endl;
    assert(0);
  }
  
  // add unsat constraint
  s.add(empty_check.end(1) == 8);
  assert(!s.check());  

  return 0;
}


// Unit test 2
int test2(){
  vector<string> alphabet_symbols {"0", "1"};

  vector<state_t> empty;
  vector<state_t> v_0_0 {1};
  vector<vector<state_t>> v_0 {v_0_0, empty};
  vector<state_t> v_1_1 {2};
  vector<vector<state_t>> v_1 {empty, v_1_1};
  vector<state_t> v_2_1 {0};
  vector<vector<state_t>> v_2 {empty, v_2_1};
  vector<vector<vector<state_t>>> tr {v_0, v_1, v_2};
  set<state_t> acc {2};
  
  NFA simple_nfa {3, 0, alphabet_symbols, tr, acc};
  assert(simple_nfa.check());
  simple_nfa.tr_rev();
  cout << simple_nfa << endl;

  context c;
  solver s(c);

  expr zero = c.int_val(0);
  vector<expr> aparikh(alphabet_symbols.size(), zero);
  for (uint a=0; a<alphabet_symbols.size(); a++){
    string name = "a_" + std::to_string(a);
    expr var = c.int_const(name.c_str());
    aparikh[a] = var;
  }

  map<uint, expr> flow_map;
  Parikh::addParikhFormula(c, s, simple_nfa, aparikh, "^1", flow_map);
  
  return 0;
}


void test_nfa_minimization(){

  uint states_no = 8;
  vector<string> alphabet {"0", "1"};

  vector<vector<vector<state_t> > > tr (states_no, vector<vector<state_t> > (alphabet.size()));
  tr[0][0].push_back(1);
  tr[0][1].push_back(5);
  tr[1][0].push_back(6);
  tr[1][1].push_back(2);
  tr[2][0].push_back(0);
  tr[2][1].push_back(2);
  tr[3][0].push_back(2);
  tr[3][1].push_back(6);
  tr[4][0].push_back(7);
  tr[4][1].push_back(5);
  tr[5][0].push_back(2);
  tr[5][1].push_back(6);
  tr[6][0].push_back(6);
  tr[6][1].push_back(4);
  tr[7][0].push_back(6);
  tr[7][1].push_back(2);

  set<state_t> acc {2};
    
  NFA nfa (states_no, 0, alphabet, tr, acc);
  assert(nfa.check());

  cout << nfa << endl;

  vector<state_t> state2eq (states_no);
  NFA nfa_min = minimize(nfa, state2eq);
  
  cout << "State -> eq mapping" << endl;
  for (uint p=0; p<states_no; p++){
    cout << p << " -> " << state2eq[p] << endl;
  }

  cout << nfa_min << endl;
  assert(nfa_min.states_no() == 5);
}



