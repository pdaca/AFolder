; based on https://raw.githubusercontent.com/vmg/redcarpet/master/ext/redcarpet/markdown.c
; character encoding 1 - '\n', 2 - '|', 3 - ':', 4 - '+', 5 -'-'
(declare-sort Arr)
(declare-sort Rel)
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_1_1 (Rel Arr Int Int Int) Bool)
(declare-fun fold_2_0 (Rel Arr Int Int Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)

; We partition the array into subarrays A0 A1;
(declare-const A0 Arr) ; A0 is from [0..i1]
(declare-const A1 Arr) ; A1 is from [i2..]

; static size_t parse_table_header(uint8_t *a, size_t size, ...)
;  size_t i=0, pipes=0;
(declare-const i0 Int)
(declare-const pipes0 Int)
(assert (= i0 0))
(assert (= pipes0 0))

;  while (i < size && a[i] != '\n')
;    if (a[i++] == '|') pipes++;
(declare-const f1 Rel)
(declare-const i1 Int)
(declare-const pipes1 Int)
(assert (fold_2_0 f1 A0 i0 pipes0 i1 pipes1))

; constraint for proper partition into A0 and A1
(declare-const len Rel)
(declare-const l0 Int)
(assert (fold_1_0 len A0 0 l0))
(assert (= l0 (+ i1 1)))

;  if (a[0] == '|') pipes--;
(declare-const f2 Rel)
(declare-const res0 Int)
(declare-const pipes2 Int)
(assert (fold_1_0 f2 A0 0 res0))
(assert (=> (= res0 0) (= pipes2 pipes1)))
(assert (=> (= res0 1) (= pipes2 (- pipes1 1))))

; i++
(declare-const i2 Int)
(assert (= i2 (+ i1 1)))

;  if (i < size && a[i] == '|') i++;
(declare-const f3 Rel)
(declare-const res1 Int)
(declare-const i3 Int)
(assert (fold_1_0 f3 A1 0 res1))
(assert (=> (= res1 0) (= i3 i2)))
(assert (=> (> res1 0) (= i3 (+ i2 1))))

;  int end = i;
(declare-const end0 Int)
(assert (= end0 i3))

;  while (end < size && a[end] != '\n') end++;
(declare-const f4 Rel)
(declare-const end1 Int)
(assert (fold_1_1 f4 A1 0 (- end1 i2) (- end0 i2)))

; -- first iteration --
; for (col = 0; col<pipes && i<end; ++col) {
;   size_t dashes = 0;
(declare-const col0 Int)
(assert (= col0 0))
(assert (< i3 end1))
(assert (< col0 pipes2))

; if (a[i] == ':') {
;   i++; dashes++; //column_data[col] |= MKD_TABLE_ALIGN_L; 
; }
;
; while (i < end && a[i] == '-') { i++; dashes++; }
;
; if (a[i] == ':') {
;   i++; dashes++; //column_data[col] |= MKD_TABLE_ALIGN_R;
; }
; if (i < end && a[i] != '|' && a[i] != '+') break;
(declare-const finner Rel)
(declare-const i4 Int)
(assert (fold_2_1 finner A1 0 0 (- i4 i2) 0 (- i3 i2)))
; dashes increase as much as index
(declare-const dashes0 Int)
(assert (= dashes0 (- i4 i3)))

; if (dashes < 3) break;
(assert (> dashes0 2))

; i++;
(declare-const i5 Int)
(assert (= i5 (+ i4 1)))

(declare-const col1 Int)
(assert (= col1 (+ col0 1)))

; no more iterations
(assert (or (>= col1 pipes2) (>= i5 end1)))

