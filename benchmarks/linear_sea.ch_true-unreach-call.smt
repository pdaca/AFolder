; int linear_search(int *a, int n, int q) {
;   unsigned int j=0;
;   while (j<n && a[j]!=q) {
;   j++;
;   }
;   if (j<SIZE) return 1;
;   else return 0;
; }
; int main() {
;   SIZE=(__VERIFIER_nondet_uint()/8)+1;
;   int a[SIZE];
;   a[SIZE/2]=3;
;   __VERIFIER_assert(linear_search(a,SIZE,3));
; }

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_1_1 (Rel Arr Int Int Int) Bool)
(declare-fun fold_1_2 (Rel Arr Int Int Int Int) Bool)
(declare-fun fold_2_2 (Rel Arr Int Int Int Int Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)

(declare-const a Arr)
(declare-const SIZE Int)
(declare-const res Int)
(declare-const any0 Int)
(declare-const any1 Int)
(declare-const len Rel)
(declare-const setval Rel)
(declare-const linear_search Rel)

(assert (fold_1_0 len a 0 SIZE))				; a[SIZE]
(assert (fold_2_1 setval a 0 0 any0 1 (/ SIZE 2)))		; a[SIZE/2] = 3
(assert (fold_2_1 linear_search a 0 0 any1 res SIZE)) 		; res = linear_search(a,SIZE,3)
(assert (= res 0))						; assert error


