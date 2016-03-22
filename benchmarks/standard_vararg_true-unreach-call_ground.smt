; int main( ){
;   int aa [100000];
;   int a = 0;
;   while( aa[a] >= 0 ) {
;     a++;
;   }
;   int x;
;   for ( x = 0 ; x < a ; x++ ) {
;     __VERIFIER_assert( aa[x] >= 0 );
;   }
;   return 0;
; }

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_2_0 (Rel Arr Int Int Int Int) Bool)

(declare-const aa Arr)
(declare-const a Int)
(declare-const res Int)
(declare-const any Int)
(declare-const len Rel)
(declare-const loop Rel)
(declare-const check Rel)

(assert (fold_1_0 len aa 0 100000))			; len of array is 100000
(assert (fold_1_0 loop aa 0 a))			        ; the while loop
(assert (fold_2_0 check aa a 0 any res))		; sets res=1 if assertion fails
(assert (= res 1))					; assert error
