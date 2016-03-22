; #define N 1024

; int main(void) {
;   int A[N];
;   int i;

;   for (i = 0; A[i] != 0; i++) {
;     if (i >= N) {
;       break;
;     }
;   }

;   __VERIFIER_assert(i <= N);
; }

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)

(declare-const A Arr)
(declare-const i Int)
(declare-const len Rel)
(declare-const loop Rel)

(assert (fold_1_0 len A 0 1024))			; len of array is 1024
(assert (fold_1_0 loop A 0 i))			        ; for loop
(assert (> i 1024))					; assert error

