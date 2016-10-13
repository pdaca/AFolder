(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_2_3 (Rel Arr Int Int Int Int Int Int Int) Bool)

(declare-const A Arr)
(declare-const find Rel)
(declare-const j Int)
(declare-const il Int)
(declare-const ih Int)
(declare-const val Int)
; check that for A[il] = val A[ih] = val
(assert (fold_2_3 find A 0 0 j 2 il ih val))
(assert (= il 0))
(assert (= ih 3))
(assert (= val 2))
