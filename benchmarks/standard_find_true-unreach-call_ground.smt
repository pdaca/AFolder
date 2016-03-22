; extern void __VERIFIER_error() __attribute__ ((__noreturn__));
; void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
; int main ( ) {
;   int a[100000]; int e;
;   int i = 0;
;   while( i < 100000 && a[i] != e ) {
;     i = i + 1;
;   }
;   int x;
;   for ( x = 0 ; x < i ; x++ ) {
;     __VERIFIER_assert( a[x] != e );
;   }
;   return 0;
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
(declare-const e Int)
(declare-const i Int)
(declare-const res Int)
(declare-const any Int)
(declare-const len Rel)
(declare-const loop Rel)
(declare-const check Rel)

(assert (fold_1_0 len a 0 100000))			; len of array is 100000
(assert (fold_1_1 loop a 0 i e))			; the while loop
(assert (fold_2_1 check a i 0 any res e))		; sets res=1 if assertion fails
(assert (= res 1))					; assert error