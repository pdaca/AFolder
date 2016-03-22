; int main ( ) {
;   int a[100000];
;   int marker;
;   int pos;
;   if ( pos >= 0 && pos < 100000 ) {
;     a[ pos ] = marker;
;     int i = 0;
;     while( a[ i ] != marker ) {
;       i = i + 1;
;     }
;     __VERIFIER_assert( i <= pos );
;   }
;   return 0;
; }

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_1_2 (Rel Arr Int Int Int Int) Bool)
(declare-fun fold_2_2 (Rel Arr Int Int Int Int Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)

(declare-const a Arr)
(declare-const marker Int)
(declare-const pos Int)
(declare-const len Rel)
(declare-const setval Rel)
(declare-const loop Rel)

(assert (fold_1_0 len a 0 100000))			; len of array is 100000
(assert (and (>= pos 0) (< pos 100000)))

(declare-const any0 Int)
(assert (fold_2_2 setval a 0 0 any0 1 pos marker))	; a[pos] = marker

(declare-const i Int)
(declare-const any1 Int)
(assert (fold_2_1 loop a 0 0 any1 i marker))		; the while loop

(assert (<= pos marker))				; implementation restriction on symbolic constants
(assert (> i pos))					; assert error
