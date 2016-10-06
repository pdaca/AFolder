(declare-sort Arr)
(declare-sort Rel)
(declare-fun fold_1_0 (Rel Arr Int Int) Bool)
(declare-fun fold_2_1 (Rel Arr Int Int Int Int Int) Bool)
(declare-const len Rel)

(declare-const A Arr) ; input array
(declare-const C Arr) ; count array

(declare-const i Int)
(declare-const j Int)
(declare-const k Int)

(declare-const I1 Bool)
(declare-const I1a Bool)	; 0<=j<=|C|
(declare-const I1b Bool)	; C[j] = fold_A(0,0)(...)

(declare-const lenC Int)
(assert (fold_1_0 len C 0 lenC))
(assert (= I1a (and (<= 0 j) (<= j lenC) )))
(assert I1a)




