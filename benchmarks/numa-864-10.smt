; static int count_process_nodes(int process_nr)
;  {
;          char node_present[MAX_NR_NODES] = { 0, };
;          int nodes;
;          int n, t;
;
;          for (t = 0; t < g->p.nr_threads; t++) {
;                  struct thread_data *td;
;                  int task_nr;
;                  int node;

;                  task_nr = process_nr*g->p.nr_threads + t;
;                  td = g->threads + task_nr;
;
;                  node = numa_node_of_cpu(td->curr_cpu);
;                  node_present[node] = 1;
;          }

;          nodes = 0;

;          for (n = 0; n < MAX_NR_NODES; n++)
;                  nodes += node_present[n];

;          return nodes;
;  }

; static void calc_convergence_compression(int *strong) {
; int p;
; nodes_min = -1;
;   nodes_max =  0;

;   for (p = 0; p < g->p.nr_proc; p++) {
;    unsigned int nodes = count_process_nodes(p);

;    nodes_min = min(nodes, nodes_min);
;    nodes_max = max(nodes, nodes_max);
;   }

;   /* Strong convergence: all threads compress on a single node: */
;   if (nodes_min == 1 && nodes_max == 1) {
;    *strong = 1;
;   } else {
;    *strong = 0;
;    tprintf(" {%d-%d}", nodes_min, nodes_max);
;   }
; }


; 

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_1_1 (Rel Arr Int Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)
(declare-fun fold_3_1 (Rel Arr Int Int Int  Int Int Int Int) Bool)

;
(declare-const count_process_nodes Rel)
(declare-const len Rel)
(declare-const MAX_NR_NODES Int)
(assert (= MAX_NR_NODES 100))

(declare-const min0 Int)
(declare-const max0 Int)
(assert (= min0 10000)) 
(assert (= max0 0))


; 1. unroaling
(declare-const min1 Int)
(declare-const max1 Int)
(declare-const nodes1 Int)
(declare-const node_present1 Arr)
(assert (fold_1_0 len node_present1 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present1 0 nodes1))
(assert (=> (< nodes1 min0) (= min1 nodes1) ))
(assert (=> (>= nodes1 min0) (= min1 min0) ))
(assert (=> (> nodes1 max0) (= max1 nodes1) ))
(assert (=> (<= nodes1 max0) (= max1 max0) ))

; 2. unroaling
(declare-const min2 Int)
(declare-const max2 Int)
(declare-const nodes2 Int)
(declare-const node_present2 Arr)
(assert (fold_1_0 len node_present2 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present2 0 nodes2))
(assert (=> (< nodes2 min1) (= min2 nodes2) ))
(assert (=> (>= nodes2 min1) (= min2 min1) ))
(assert (=> (> nodes2 max1) (= max2 nodes2) ))
(assert (=> (<= nodes2 max1) (= max2 max1) ))

; 3. unroaling
(declare-const min3 Int)
(declare-const max3 Int)
(declare-const nodes3 Int)
(declare-const node_present3 Arr)
(assert (fold_1_0 len node_present3 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present3 0 nodes3))
(assert (=> (< nodes3 min2) (= min3 nodes3) ))
(assert (=> (>= nodes3 min2) (= min3 min2) ))
(assert (=> (> nodes3 max2) (= max3 nodes3) ))
(assert (=> (<= nodes3 max2) (= max3 max2) ))


; 4. unroaling
(declare-const min4 Int)
(declare-const max4 Int)
(declare-const nodes4 Int)
(declare-const node_present4 Arr)
(assert (fold_1_0 len node_present4 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present4 0 nodes4))
(assert (=> (< nodes4 min3) (= min4 nodes4) ))
(assert (=> (>= nodes4 min3) (= min4 min3) ))
(assert (=> (> nodes4 max3) (= max4 nodes4) ))
(assert (=> (<= nodes4 max3) (= max4 max3) ))

; 5. unroaling
(declare-const min5 Int)
(declare-const max5 Int)
(declare-const nodes5 Int)
(declare-const node_present5 Arr)
(assert (fold_1_0 len node_present5 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present5 0 nodes5))
(assert (=> (< nodes5 min4) (= min5 nodes5) ))
(assert (=> (>= nodes5 min4) (= min5 min4) ))
(assert (=> (> nodes5 max4) (= max5 nodes5) ))
(assert (=> (<= nodes5 max4) (= max5 max4) ))

; 6. unroaling
(declare-const min6 Int)
(declare-const max6 Int)
(declare-const nodes6 Int)
(declare-const node_present6 Arr)
(assert (fold_1_0 len node_present6 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present6 0 nodes6))
(assert (=> (< nodes6 min5) (= min6 nodes6) ))
(assert (=> (>= nodes6 min5) (= min6 min5) ))
(assert (=> (> nodes6 max5) (= max6 nodes6) ))
(assert (=> (<= nodes6 max5) (= max6 max5) ))

; 7. unroaling
(declare-const min7 Int)
(declare-const max7 Int)
(declare-const nodes7 Int)
(declare-const node_present7 Arr)
(assert (fold_1_0 len node_present7 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present7 0 nodes7))
(assert (=> (< nodes7 min6) (= min7 nodes7) ))
(assert (=> (>= nodes7 min6) (= min7 min6) ))
(assert (=> (> nodes7 max6) (= max7 nodes7) ))
(assert (=> (<= nodes7 max6) (= max7 max6) ))

; 8. unroaling
(declare-const min8 Int)
(declare-const max8 Int)
(declare-const nodes8 Int)
(declare-const node_present8 Arr)
(assert (fold_1_0 len node_present8 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present8 0 nodes8))
(assert (=> (< nodes8 min7) (= min8 nodes8) ))
(assert (=> (>= nodes8 min7) (= min8 min7) ))
(assert (=> (> nodes8 max7) (= max8 nodes8) ))
(assert (=> (<= nodes8 max7) (= max8 max7) ))

; 9. unroaling
(declare-const min9 Int)
(declare-const max9 Int)
(declare-const nodes9 Int)
(declare-const node_present9 Arr)
(assert (fold_1_0 len node_present9 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present9 0 nodes9))
(assert (=> (< nodes9 min8) (= min9 nodes9) ))
(assert (=> (>= nodes9 min8) (= min9 min8) ))
(assert (=> (> nodes9 max8) (= max9 nodes9) ))
(assert (=> (<= nodes9 max8) (= max9 max8) ))

; 10. unroaling
(declare-const min10 Int)
(declare-const max10 Int)
(declare-const nodes10 Int)
(declare-const node_present10 Arr)
(assert (fold_1_0 len node_present10 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present10 0 nodes10))
(assert (=> (< nodes10 min9) (= min10 nodes10) ))
(assert (=> (>= nodes10 min9) (= min10 min9) ))
(assert (=> (> nodes10 max9) (= max10 nodes10) ))
(assert (=> (<= nodes10 max9) (= max10 max9) ))

(assert (= min10 1))
(assert (= max10 1))