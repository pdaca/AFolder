; Compute a histogram in 5 buckets

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_1_1 (Rel Arr Int Int Int) Bool)
(declare-fun fold_1_2 (Rel Arr Int Int Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)
(declare-fun fold_2_2 (Rel Arr Int Int Int Int Int Int) Bool)

(declare-const data Arr)
(declare-const count Rel)
(declare-const count_open Rel)

(declare-const i Int)

(declare-const sub_size Int)
(assert (= sub_size 10))

(assert (fold_1_2 count data 0 i 0 sub_size))

(assert (fold_1_2 count data 0 i sub_size (* 2 sub_size)))

(assert (fold_1_2 count data 0 i (* 2 sub_size) (* 3 sub_size)))

(assert (fold_1_2 count data 0 i (* 3 sub_size) (* 4 sub_size)))

(assert (fold_1_2 count data 0 i (* 4 sub_size) (* 5 sub_size)))

(assert (fold_1_1 count_open data 0 i (* 5 sub_size)))

(assert (> i 0))


