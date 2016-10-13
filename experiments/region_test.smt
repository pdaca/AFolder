; dummy test for checking if the solver correctly finds regions
(declare-sort Arr)
(declare-sort Rel)
; fold_m_n means a fold over m counters with n symbolic constants
(declare-fun fold_3_3 (Rel Arr Int Int Int Int Int Int Int Int Int) Bool)

(declare-const A Arr)
(declare-const i1 Int)
(declare-const i2 Int)
(declare-const i3 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const foo Rel)

(assert (fold_3_3 foo A 0 0 0 i1 i2 i3 x1 x2 x3))