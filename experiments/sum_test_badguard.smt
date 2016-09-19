; invalid guard for incrementing a counter by an array element
; #define N 30

; int main(void) {
;   int A[N];
;   int i;
;   int sum;
;
;   for (i = 0; A[i] != 0; i++) {
;     if (A[i]>=-2) {
;       sum =+ A[i];
;     }
;   }

;   __VERIFIER_assert(sum == 100);
; }

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)

(declare-const A Arr)
(declare-const sum Int)
(declare-const len Rel)
(declare-const loop Rel)

(assert (fold_1_0 len A 0 30))			; len of array is 1024
(assert (fold_1_0 loop A 0 sum))			; for loop
(assert (= sum 100))					; assert error

