; incorrect version that mixes updating counter by an array element and comparing the element to symbolic constant in the same action
; #define N 30

; int main(void) {
;   int A[N];
;   int i;
;   int sum;
;   int s;
;
;   for (i = 0; A[i] != 0; i++) {
;     if (A[i]>=0 && A[i]>=s) {
;       sum =+ A[i];
;     }
;   }

;   __VERIFIER_assert(sum == 100);
; }

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_1 (Rel Arr Int Int Int) Bool)

(declare-const A Arr)
(declare-const sum Int)
(declare-const s Int)
(declare-const len Rel)
(declare-const loop Rel)

(assert (fold_1_0 len A 0 30))			; len of array is 1024
(assert (fold_1_0 loop A 0 sum s))			; for loop
(assert (= sum 100))					; assert error

