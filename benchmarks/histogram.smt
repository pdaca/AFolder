; Compute a histogram

(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)
(declare-fun fold_2_2 (Rel Arr Int Int Int Int Int Int) Bool)

(declare-const data Arr)
(declare-const count Rel)

(declare-const i Int)

(declare-const sub_size Int)
(assert (= sub_size 10))

(declare-const i0 Int)
(declare-const any0 Int)
; i is the number of positive elements in the subarray [0, sub_size-1]
(assert (fold_2_2 count data 0 0 i any0 0 (- sub_size 1)))
; i is the number of positive elements in the subarray [sub_size, 2*sub_size-1]
(assert (fold_2_2 count data 0 0 i any0 sub_size (- (* sub_size 2) 1)))
; i is the number of positive elements in the subarray [2*sub_size, 3*sub_size-1]
(assert (fold_2_2 count data 0 0 i any0 (* 2sub_size) (- (* sub_size 3) 1)))

(assert (= i 2))


