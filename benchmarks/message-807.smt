o; from ./drivers/isdn/hardware/eicon/message.c-807
; i = 1;
; do
; {
; 	j = 1;	
; 	while ((j < MAX_NCCI + 1) && (a->ncci_ch[j] != i))
; 	      j++;

;  	k = j;
; 	if (j < MAX_NCCI + 1)
; 	{
; 		do
; 		{
; 			j++;
; 		} while ((j < MAX_NCCI + 1) && (a->ncci_ch[j] != i));
; 	}

; } while ((i < MAX_NL_CHANNEL + 1) && (j < MAX_NCCI + 1));

; if (i < MAX_NL_CHANNEL + 1)
; {
; 	dbug(1, dprintf("NCCI mapping overflow %ld %02x %02x %02x-%02x-%02x",
; 	ncci_mapping_bug, ch, force_ncci, i, k, j));
; }
; else
; {
;	dbug(1, dprintf("NCCI mapping overflow %ld %02x %02x",
;	ncci_mapping_bug, ch, force_ncci));
; }



(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_1_1 (Rel Arr Int Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)
(declare-fun fold_3_1 (Rel Arr Int Int Int  Int Int Int Int) Bool)

(declare-const ncchi_ch Arr)
(declare-const while Rel)		; the inner while loops. 
(declare-const len Rel)			; length of array

(declare-const MAX_NCCI Int)
(declare-const MAX_NL_CHANNEL Int)
(declare-const l Int)
(assert (fold_1_0 len ncchi_ch 0 l))	
(assert (> l 10))			; set the array to be non-trivial
(assert (= MAX_NCCI 127))
(assert (= MAX_NL_CHANNEL 255))

(declare-const i0 Int)
(assert (= i0 1))

;
; 1.st loop unroaling
;
(declare-const j0 Int)
(assert (= j0 1))

(declare-const j1 Int)
(declare-const any0 Int)
(declare-const any1 Int)
(assert (fold_3_1 while ncchi_ch j0 (+ MAX_NCCI 1) 0 any0 any1 j1 i0))	 	; j1 is the value after the 1st. inner while loop

(declare-const j2 Int)
(declare-const j3 Int)

(declare-const any2 Int)
(declare-const any3 Int)
;(assert (fold_3_1 while ncchi_ch (+ j1 1) (+ MAX_NCCI 1) 0 any2 any3 j2 i0))	; j2 is the value after the 2st. inner while loop (if executed0

(assert (=> (< j1 (+ MAX_NCCI 1)) (= j3 j2)))					; j3 is the value after one iteration of the for loop
(assert (=> (>= j1 (+ MAX_NCCI 1)) (= j3 j1)))

(assert (>= j3 (+ MAX_NCCI 1)))
