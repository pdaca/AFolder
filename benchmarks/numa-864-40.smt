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


; 11. unroaling
(declare-const min11 Int)
(declare-const max11 Int)
(declare-const nodes11 Int)
(declare-const node_present11 Arr)
(assert (fold_1_0 len node_present11 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present11 0 nodes11))
(assert (=> (< nodes11 min10) (= min11 nodes11) ))
(assert (=> (>= nodes11 min10) (= min11 min10) ))
(assert (=> (> nodes11 max10) (= max11 nodes11) ))
(assert (=> (<= nodes11 max10) (= max11 max10) ))

; 12. unroaling
(declare-const min12 Int)
(declare-const max12 Int)
(declare-const nodes12 Int)
(declare-const node_present12 Arr)
(assert (fold_1_0 len node_present12 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present12 0 nodes12))
(assert (=> (< nodes12 min11) (= min12 nodes12) ))
(assert (=> (>= nodes12 min11) (= min12 min11) ))
(assert (=> (> nodes12 max11) (= max12 nodes12) ))
(assert (=> (<= nodes12 max11) (= max12 max11) ))

; 13. unroaling
(declare-const min13 Int)
(declare-const max13 Int)
(declare-const nodes13 Int)
(declare-const node_present13 Arr)
(assert (fold_1_0 len node_present13 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present13 0 nodes13))
(assert (=> (< nodes13 min12) (= min13 nodes13) ))
(assert (=> (>= nodes13 min12) (= min13 min12) ))
(assert (=> (> nodes13 max12) (= max13 nodes13) ))
(assert (=> (<= nodes13 max12) (= max13 max12) ))

; 14. unroaling
(declare-const min14 Int)
(declare-const max14 Int)
(declare-const nodes14 Int)
(declare-const node_present14 Arr)
(assert (fold_1_0 len node_present14 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present14 0 nodes14))
(assert (=> (< nodes14 min13) (= min14 nodes14) ))
(assert (=> (>= nodes14 min13) (= min14 min13) ))
(assert (=> (> nodes14 max13) (= max14 nodes14) ))
(assert (=> (<= nodes14 max13) (= max14 max13) ))

; 15. unroaling
(declare-const min15 Int)
(declare-const max15 Int)
(declare-const nodes15 Int)
(declare-const node_present15 Arr)
(assert (fold_1_0 len node_present15 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present15 0 nodes15))
(assert (=> (< nodes15 min14) (= min15 nodes15) ))
(assert (=> (>= nodes15 min14) (= min15 min14) ))
(assert (=> (> nodes15 max14) (= max15 nodes15) ))
(assert (=> (<= nodes15 max14) (= max15 max14) ))

; 16. unroaling
(declare-const min16 Int)
(declare-const max16 Int)
(declare-const nodes16 Int)
(declare-const node_present16 Arr)
(assert (fold_1_0 len node_present16 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present16 0 nodes16))
(assert (=> (< nodes16 min15) (= min16 nodes16) ))
(assert (=> (>= nodes16 min15) (= min16 min15) ))
(assert (=> (> nodes16 max15) (= max16 nodes16) ))
(assert (=> (<= nodes16 max15) (= max16 max15) ))

; 17. unroaling
(declare-const min17 Int)
(declare-const max17 Int)
(declare-const nodes17 Int)
(declare-const node_present17 Arr)
(assert (fold_1_0 len node_present17 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present17 0 nodes17))
(assert (=> (< nodes17 min16) (= min17 nodes17) ))
(assert (=> (>= nodes17 min16) (= min17 min16) ))
(assert (=> (> nodes17 max16) (= max17 nodes17) ))
(assert (=> (<= nodes17 max16) (= max17 max16) ))

; 18. unroaling
(declare-const min18 Int)
(declare-const max18 Int)
(declare-const nodes18 Int)
(declare-const node_present18 Arr)
(assert (fold_1_0 len node_present18 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present18 0 nodes18))
(assert (=> (< nodes18 min17) (= min18 nodes18) ))
(assert (=> (>= nodes18 min17) (= min18 min17) ))
(assert (=> (> nodes18 max17) (= max18 nodes18) ))
(assert (=> (<= nodes18 max17) (= max18 max17) ))

; 19. unroaling
(declare-const min19 Int)
(declare-const max19 Int)
(declare-const nodes19 Int)
(declare-const node_present19 Arr)
(assert (fold_1_0 len node_present19 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present19 0 nodes19))
(assert (=> (< nodes19 min18) (= min19 nodes19) ))
(assert (=> (>= nodes19 min18) (= min19 min18) ))
(assert (=> (> nodes19 max18) (= max19 nodes19) ))
(assert (=> (<= nodes19 max18) (= max19 max18) ))

; 20. unroaling
(declare-const min20 Int)
(declare-const max20 Int)
(declare-const nodes20 Int)
(declare-const node_present20 Arr)
(assert (fold_1_0 len node_present20 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present20 0 nodes20))
(assert (=> (< nodes20 min19) (= min20 nodes20) ))
(assert (=> (>= nodes20 min19) (= min20 min19) ))
(assert (=> (> nodes20 max19) (= max20 nodes20) ))
(assert (=> (<= nodes20 max19) (= max20 max19) ))

; 21. unroaling
(declare-const min22 Int)
(declare-const max22 Int)
(declare-const nodes22 Int)
(declare-const node_present22 Arr)
(assert (fold_1_0 len node_present22 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present22 0 nodes22))
(assert (=> (< nodes22 min20) (= min22 nodes22) ))
(assert (=> (>= nodes22 min20) (= min22 min20) ))
(assert (=> (> nodes22 max20) (= max22 nodes22) ))
(assert (=> (<= nodes22 max20) (= max22 max20) ))

; 22. unroaling
(declare-const min22 Int)
(declare-const max22 Int)
(declare-const nodes22 Int)
(declare-const node_present22 Arr)
(assert (fold_1_0 len node_present22 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present22 0 nodes22))
(assert (=> (< nodes22 min22) (= min22 nodes22) ))
(assert (=> (>= nodes22 min22) (= min22 min22) ))
(assert (=> (> nodes22 max22) (= max22 nodes22) ))
(assert (=> (<= nodes22 max22) (= max22 max22) ))

; 23. unroaling
(declare-const min23 Int)
(declare-const max23 Int)
(declare-const nodes23 Int)
(declare-const node_present23 Arr)
(assert (fold_1_0 len node_present23 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present23 0 nodes23))
(assert (=> (< nodes23 min22) (= min23 nodes23) ))
(assert (=> (>= nodes23 min22) (= min23 min22) ))
(assert (=> (> nodes23 max22) (= max23 nodes23) ))
(assert (=> (<= nodes23 max22) (= max23 max22) ))

; 24. unroaling
(declare-const min24 Int)
(declare-const max24 Int)
(declare-const nodes24 Int)
(declare-const node_present24 Arr)
(assert (fold_1_0 len node_present24 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present24 0 nodes24))
(assert (=> (< nodes24 min23) (= min24 nodes24) ))
(assert (=> (>= nodes24 min23) (= min24 min23) ))
(assert (=> (> nodes24 max23) (= max24 nodes24) ))
(assert (=> (<= nodes24 max23) (= max24 max23) ))

; 25. unroaling
(declare-const min25 Int)
(declare-const max25 Int)
(declare-const nodes25 Int)
(declare-const node_present25 Arr)
(assert (fold_1_0 len node_present25 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present25 0 nodes25))
(assert (=> (< nodes25 min24) (= min25 nodes25) ))
(assert (=> (>= nodes25 min24) (= min25 min24) ))
(assert (=> (> nodes25 max24) (= max25 nodes25) ))
(assert (=> (<= nodes25 max24) (= max25 max24) ))

; 26. unroaling
(declare-const min26 Int)
(declare-const max26 Int)
(declare-const nodes26 Int)
(declare-const node_present26 Arr)
(assert (fold_1_0 len node_present26 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present26 0 nodes26))
(assert (=> (< nodes26 min25) (= min26 nodes26) ))
(assert (=> (>= nodes26 min25) (= min26 min25) ))
(assert (=> (> nodes26 max25) (= max26 nodes26) ))
(assert (=> (<= nodes26 max25) (= max26 max25) ))

; 27. unroaling
(declare-const min27 Int)
(declare-const max27 Int)
(declare-const nodes27 Int)
(declare-const node_present27 Arr)
(assert (fold_1_0 len node_present27 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present27 0 nodes27))
(assert (=> (< nodes27 min26) (= min27 nodes27) ))
(assert (=> (>= nodes27 min26) (= min27 min26) ))
(assert (=> (> nodes27 max26) (= max27 nodes27) ))
(assert (=> (<= nodes27 max26) (= max27 max26) ))

; 28. unroaling
(declare-const min28 Int)
(declare-const max28 Int)
(declare-const nodes28 Int)
(declare-const node_present28 Arr)
(assert (fold_1_0 len node_present28 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present28 0 nodes28))
(assert (=> (< nodes28 min27) (= min28 nodes28) ))
(assert (=> (>= nodes28 min27) (= min28 min27) ))
(assert (=> (> nodes28 max27) (= max28 nodes28) ))
(assert (=> (<= nodes28 max27) (= max28 max27) ))

; 29. unroaling
(declare-const min29 Int)
(declare-const max29 Int)
(declare-const nodes29 Int)
(declare-const node_present29 Arr)
(assert (fold_1_0 len node_present29 0 MAX_NR_NODES))
(assert (fold_1_0 count_process_nodes node_present29 0 nodes29))
(assert (=> (< nodes29 min28) (= min29 nodes29) ))
(assert (=> (>= nodes29 min28) (= min29 min28) ))
(assert (=> (> nodes29 max28) (= max29 nodes29) ))
(assert (=> (<= nodes29 max28) (= max29 max28) ))


(assert (= min29 2))
(assert (= max29 2))