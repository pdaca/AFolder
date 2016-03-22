(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_1_1 (Rel Arr Int Int Int) Bool)

; int main( ) {
;   int a[N];
;   int min = 0;
;   int i = 0;
;   while ( i < N ) {
;     if ( a[i] < min ) {
;       min = a[i];
;     }
;     i = i + 1;
;   }

;   int x;
;   for ( x = 0 ; x < N ; x++ ) {
;     __VERIFIER_assert(  a[x] > min  );
;   }
;   return 0;
; }

(declare-const a Arr)
(declare-const find_min Rel)
(declare-const assert_min Rel)
(declare-const len Rel)
(declare-const m Int)

(assert (fold_1_1 find_min a 0 1 m)) 	; m is the min element
(assert (fold_1_0 len a 0 100000))	; length is 100000
(assert (fold_1_1 assert_min a 0 1 m))	; 



