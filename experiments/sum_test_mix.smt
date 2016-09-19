; #define N 30

; int main(void) {
;   int A[N];
;   int i;
;   int r;
;   int sum, c;
;
;   for (i = 0; A[i] != 0; i++) {
;     if (A[i]>=0) {
;       sum =+ A[i];
;     }
;   }
;
;  if (A[i] == r && r < 0) c++;
;
;   __VERIFIER_assert(sum == 100);
;   __VERIFIER_assert(c = 3);
; }

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)

(declare-const A Arr)
(declare-const sum Int)
(declare-const c Int)
(declare-const r Int)
(declare-const len Rel)
(declare-const loop Rel)

(assert (fold_1_0 len A 0 30))			; len of array is 1024
(assert (fold_2_1 loop A 0 0 sum c r))			; for loop
(assert (= sum 100))					; assert error
(assert (= c 3))

