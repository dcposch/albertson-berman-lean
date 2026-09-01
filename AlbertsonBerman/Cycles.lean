import AlbertsonBerman.ForestBound
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

open Finset SimpleGraph AlbertsonBerman

namespace AlbertsonBerman

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def xEdges : Finset (Sym2 (Fin 14)) :=
  {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6), s(1, 2),
   s(1, 6), s(1, 7), s(1, 8), s(1, 9), s(2, 3), s(2, 9), s(2, 10),
   s(3, 4), s(3, 10), s(3, 11), s(4, 5), s(4, 11), s(4, 12), s(5, 6),
   s(5, 7), s(5, 8), s(5, 12), s(6, 7), s(7, 8), s(8, 9), s(8, 12),
   s(8, 13), s(9, 10), s(9, 13), s(10, 11), s(10, 13), s(11, 12), s(11, 13),
   s(12, 13)}

def X : SimpleGraph (Fin 14) := fromEdgeSet (xEdges : Set _)

instance : DecidableRel X.Adj := by
  unfold X
  infer_instance

def bEdges : Finset (Sym2 (Fin 7)) :=
  {s(0, 1), s(0, 4), s(0, 5), s(0, 6), s(1, 2), s(1, 5), s(1, 6),
   s(2, 3), s(2, 5), s(2, 6), s(3, 4), s(3, 5), s(3, 6), s(4, 5), s(4, 6)}

def B : SimpleGraph (Fin 7) := fromEdgeSet (bEdges : Set _)

instance : DecidableRel B.Adj := by
  unfold B
  infer_instance


lemma x_empty_0 : ¬ (X.induce ({0, 1, 3, 5, 8, 10, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 8) (.cons (by decide : X.Adj 8 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_1 : ¬ (X.induce ({0, 1, 3, 5, 8, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 8) (.cons (by decide : X.Adj 8 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_2 : ¬ (X.induce ({0, 1, 3, 5, 9, 10, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 3) (.cons (by decide : X.Adj 3 10) (.cons (by decide : X.Adj 10 9) (.cons (by decide : X.Adj 9 1) (.cons (by decide : X.Adj 1 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_3 : ¬ (X.induce ({0, 1, 3, 5, 9, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 12) (.cons (by decide : X.Adj 12 11) (.cons (by decide : X.Adj 11 3) (.cons (by decide : X.Adj 3 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_4 : ¬ (X.induce ({0, 1, 3, 5, 9, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 3) (.cons (by decide : X.Adj 3 11) (.cons (by decide : X.Adj 11 13) (.cons (by decide : X.Adj 13 9) (.cons (by decide : X.Adj 9 1) (.cons (by decide : X.Adj 1 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_5 : ¬ (X.induce ({0, 1, 3, 5, 9, 12, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 12) (.cons (by decide : X.Adj 12 13) (.cons (by decide : X.Adj 13 9) (.cons (by decide : X.Adj 9 1) (.cons (by decide : X.Adj 1 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_6 : ¬ (X.induce ({0, 1, 3, 5, 10, 12, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 12) (.cons (by decide : X.Adj 12 13) (.cons (by decide : X.Adj 13 10) (.cons (by decide : X.Adj 10 3) (.cons (by decide : X.Adj 3 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_7 : ¬ (X.induce ({0, 1, 5, 9, 10, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 12) (.cons (by decide : X.Adj 12 11) (.cons (by decide : X.Adj 11 10) (.cons (by decide : X.Adj 10 9) (.cons (by decide : X.Adj 9 1) (.cons (by decide : X.Adj 1 0) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_8 : ¬ (X.induce ({1, 2, 3, 4, 5, 8, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 5) (.cons (by decide : X.Adj 5 4) (.cons (by decide : X.Adj 4 3) (.cons (by decide : X.Adj 3 2) (.cons (by decide : X.Adj 2 1) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_9 : ¬ (X.induce ({1, 2, 3, 5, 8, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 11) (.cons (by decide : X.Adj 11 3) (.cons (by decide : X.Adj 3 2) (.cons (by decide : X.Adj 2 1) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_10 : ¬ (X.induce ({1, 2, 4, 5, 8, 10, 11} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 5) (.cons (by decide : X.Adj 5 4) (.cons (by decide : X.Adj 4 11) (.cons (by decide : X.Adj 11 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 1) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_11 : ¬ (X.induce ({1, 2, 4, 5, 8, 10, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 1) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_12 : ¬ (X.induce ({1, 2, 4, 5, 8, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 8 8 := .cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 11) (.cons (by decide : X.Adj 11 4) (.cons (by decide : X.Adj 4 5) (.cons (by decide : X.Adj 5 8) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_empty_13 : ¬ (X.induce ({1, 3, 4, 5, 8, 10, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 8 8 := .cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 10) (.cons (by decide : X.Adj 10 3) (.cons (by decide : X.Adj 3 4) (.cons (by decide : X.Adj 4 5) (.cons (by decide : X.Adj 5 8) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_g_0 : ¬ (X.induce ({1, 2, 3, 4, 5, 6, 8, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 6) (.cons (by decide : X.Adj 6 5) (.cons (by decide : X.Adj 5 4) (.cons (by decide : X.Adj 4 3) (.cons (by decide : X.Adj 3 2) (.cons (by decide : X.Adj 2 1) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_g_1 : ¬ (X.induce ({1, 2, 3, 5, 6, 8, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 11) (.cons (by decide : X.Adj 11 3) (.cons (by decide : X.Adj 3 2) (.cons (by decide : X.Adj 2 1) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_g_2 : ¬ (X.induce ({1, 2, 4, 5, 6, 8, 10, 11} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 6) (.cons (by decide : X.Adj 6 5) (.cons (by decide : X.Adj 5 4) (.cons (by decide : X.Adj 4 11) (.cons (by decide : X.Adj 11 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 1) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_g_3 : ¬ (X.induce ({1, 2, 4, 5, 6, 8, 10, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 1) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_g_4 : ¬ (X.induce ({1, 2, 4, 5, 6, 8, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 11) (.cons (by decide : X.Adj 11 4) (.cons (by decide : X.Adj 4 5) (.cons (by decide : X.Adj 5 6) (.cons (by decide : X.Adj 6 1) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_g_5 : ¬ (X.induce ({1, 3, 4, 5, 6, 8, 10, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 1 1 := .cons (by decide : X.Adj 1 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 10) (.cons (by decide : X.Adj 10 3) (.cons (by decide : X.Adj 3 4) (.cons (by decide : X.Adj 4 5) (.cons (by decide : X.Adj 5 6) (.cons (by decide : X.Adj 6 1) (.nil))))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_h_0 : ¬ (X.induce ({0, 1, 3, 5, 7, 9, 10, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 7) (.cons (by decide : X.Adj 7 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_h_1 : ¬ (X.induce ({0, 1, 3, 5, 7, 9, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 7) (.cons (by decide : X.Adj 7 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_h_2 : ¬ (X.induce ({0, 1, 3, 5, 7, 9, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 7) (.cons (by decide : X.Adj 7 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_h_3 : ¬ (X.induce ({0, 1, 3, 5, 7, 9, 12, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 7) (.cons (by decide : X.Adj 7 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_h_4 : ¬ (X.induce ({0, 1, 3, 5, 7, 10, 12, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 7) (.cons (by decide : X.Adj 7 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_h_5 : ¬ (X.induce ({0, 1, 5, 7, 9, 10, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 5) (.cons (by decide : X.Adj 5 7) (.cons (by decide : X.Adj 7 1) (.cons (by decide : X.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_0 : ¬ (X.induce ({0, 2, 4, 6, 7, 8, 9, 11} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 9) (.cons (by decide : X.Adj 9 2) (.cons (by decide : X.Adj 2 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_1 : ¬ (X.induce ({0, 2, 4, 6, 7, 8, 9, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 9) (.cons (by decide : X.Adj 9 2) (.cons (by decide : X.Adj 2 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_2 : ¬ (X.induce ({0, 2, 4, 6, 7, 8, 10, 11} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 4) (.cons (by decide : X.Adj 4 11) (.cons (by decide : X.Adj 11 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_3 : ¬ (X.induce ({0, 2, 4, 6, 7, 8, 10, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 4) (.cons (by decide : X.Adj 4 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_4 : ¬ (X.induce ({0, 2, 4, 6, 7, 8, 10, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 0) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_5 : ¬ (X.induce ({0, 2, 4, 6, 7, 8, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 13) (.cons (by decide : X.Adj 13 11) (.cons (by decide : X.Adj 11 4) (.cons (by decide : X.Adj 4 0) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_6 : ¬ (X.induce ({0, 2, 4, 6, 7, 9, 11, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 4) (.cons (by decide : X.Adj 4 11) (.cons (by decide : X.Adj 11 13) (.cons (by decide : X.Adj 13 9) (.cons (by decide : X.Adj 9 2) (.cons (by decide : X.Adj 2 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_7 : ¬ (X.induce ({0, 2, 4, 6, 7, 9, 12, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 4) (.cons (by decide : X.Adj 4 12) (.cons (by decide : X.Adj 12 13) (.cons (by decide : X.Adj 13 9) (.cons (by decide : X.Adj 9 2) (.cons (by decide : X.Adj 2 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_8 : ¬ (X.induce ({0, 2, 4, 6, 7, 10, 12, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 4) (.cons (by decide : X.Adj 4 12) (.cons (by decide : X.Adj 12 13) (.cons (by decide : X.Adj 13 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_9 : ¬ (X.induce ({0, 2, 6, 7, 8, 9, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 9) (.cons (by decide : X.Adj 9 2) (.cons (by decide : X.Adj 2 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_10 : ¬ (X.induce ({0, 2, 6, 7, 8, 10, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 11) (.cons (by decide : X.Adj 11 10) (.cons (by decide : X.Adj 10 2) (.cons (by decide : X.Adj 2 0) (.nil))))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_11 : ¬ (X.induce ({0, 3, 6, 7, 8, 9, 10, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 9) (.cons (by decide : X.Adj 9 10) (.cons (by decide : X.Adj 10 3) (.cons (by decide : X.Adj 3 0) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_12 : ¬ (X.induce ({0, 3, 6, 7, 8, 9, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 11) (.cons (by decide : X.Adj 11 3) (.cons (by decide : X.Adj 3 0) (.nil)))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_13 : ¬ (X.induce ({0, 4, 6, 7, 8, 9, 10, 11} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 9) (.cons (by decide : X.Adj 9 10) (.cons (by decide : X.Adj 10 11) (.cons (by decide : X.Adj 11 4) (.cons (by decide : X.Adj 4 0) (.nil))))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_14 : ¬ (X.induce ({0, 4, 6, 7, 8, 9, 10, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 0 0 := .cons (by decide : X.Adj 0 6) (.cons (by decide : X.Adj 6 7) (.cons (by decide : X.Adj 7 8) (.cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 4) (.cons (by decide : X.Adj 4 0) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_15 : ¬ (X.induce ({0, 6, 7, 8, 9, 10, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 8 8 := .cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 11) (.cons (by decide : X.Adj 11 10) (.cons (by decide : X.Adj 10 9) (.cons (by decide : X.Adj 9 8) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_16 : ¬ (X.induce ({2, 3, 4, 6, 7, 8, 9, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 2 2 := .cons (by decide : X.Adj 2 9) (.cons (by decide : X.Adj 9 8) (.cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 4) (.cons (by decide : X.Adj 4 3) (.cons (by decide : X.Adj 3 2) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_17 : ¬ (X.induce ({2, 3, 4, 6, 7, 9, 12, 13} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 2 2 := .cons (by decide : X.Adj 2 9) (.cons (by decide : X.Adj 9 13) (.cons (by decide : X.Adj 13 12) (.cons (by decide : X.Adj 12 4) (.cons (by decide : X.Adj 4 3) (.cons (by decide : X.Adj 3 2) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_18 : ¬ (X.induce ({2, 3, 6, 7, 8, 9, 11, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 2 2 := .cons (by decide : X.Adj 2 9) (.cons (by decide : X.Adj 9 8) (.cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 11) (.cons (by decide : X.Adj 11 3) (.cons (by decide : X.Adj 3 2) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma x_gh_19 : ¬ (X.induce ({3, 4, 6, 7, 8, 9, 10, 12} : Set (Fin 14))).IsAcyclic := by
  let w : X.Walk 3 3 := .cons (by decide : X.Adj 3 10) (.cons (by decide : X.Adj 10 9) (.cons (by decide : X.Adj 9 8) (.cons (by decide : X.Adj 8 12) (.cons (by decide : X.Adj 12 4) (.cons (by decide : X.Adj 4 3) (.nil))))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_0 : ¬ (B.induce ({0, 2, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_1 : ¬ (B.induce ({1, 2, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 1) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_2 : ¬ (B.induce ({0, 1, 2, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_3 : ¬ (B.induce ({0, 3, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 3) (.cons (by decide : B.Adj 3 4) (.cons (by decide : B.Adj 4 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_4 : ¬ (B.induce ({1, 3, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 5 5 := .cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 5) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_5 : ¬ (B.induce ({0, 1, 3, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 1) (.cons (by decide : B.Adj 1 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_6 : ¬ (B.induce ({0, 2, 3, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 3) (.cons (by decide : B.Adj 3 4) (.cons (by decide : B.Adj 4 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_7 : ¬ (B.induce ({1, 2, 3, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 5) (.cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_8 : ¬ (B.induce ({0, 1, 2, 3, 4, 5} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_9 : ¬ (B.induce ({0, 2, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 6) (.cons (by decide : B.Adj 6 4) (.cons (by decide : B.Adj 4 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_10 : ¬ (B.induce ({1, 2, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 6) (.cons (by decide : B.Adj 6 2) (.cons (by decide : B.Adj 2 1) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_11 : ¬ (B.induce ({0, 1, 2, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 6) (.cons (by decide : B.Adj 6 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_12 : ¬ (B.induce ({0, 3, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 6) (.cons (by decide : B.Adj 6 3) (.cons (by decide : B.Adj 3 4) (.cons (by decide : B.Adj 4 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_13 : ¬ (B.induce ({1, 3, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 6 6 := .cons (by decide : B.Adj 6 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 6) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_14 : ¬ (B.induce ({0, 1, 3, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 6) (.cons (by decide : B.Adj 6 1) (.cons (by decide : B.Adj 1 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_15 : ¬ (B.induce ({0, 2, 3, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 6) (.cons (by decide : B.Adj 6 2) (.cons (by decide : B.Adj 2 3) (.cons (by decide : B.Adj 3 4) (.cons (by decide : B.Adj 4 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_16 : ¬ (B.induce ({1, 2, 3, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 6) (.cons (by decide : B.Adj 6 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_17 : ¬ (B.induce ({0, 1, 2, 3, 4, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_18 : ¬ (B.induce ({0, 2, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 6) (.cons (by decide : B.Adj 6 2) (.cons (by decide : B.Adj 2 5) (.cons (by decide : B.Adj 5 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_19 : ¬ (B.induce ({1, 2, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 1) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_20 : ¬ (B.induce ({0, 1, 2, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_21 : ¬ (B.induce ({0, 3, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 6) (.cons (by decide : B.Adj 6 3) (.cons (by decide : B.Adj 3 5) (.cons (by decide : B.Adj 5 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_22 : ¬ (B.induce ({1, 3, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 6) (.cons (by decide : B.Adj 6 3) (.cons (by decide : B.Adj 3 5) (.cons (by decide : B.Adj 5 1) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_23 : ¬ (B.induce ({0, 1, 3, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 1) (.cons (by decide : B.Adj 1 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_24 : ¬ (B.induce ({0, 2, 3, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 5 5 := .cons (by decide : B.Adj 5 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 5) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_25 : ¬ (B.induce ({1, 2, 3, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 5) (.cons (by decide : B.Adj 5 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_26 : ¬ (B.induce ({0, 1, 2, 3, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_27 : ¬ (B.induce ({0, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_28 : ¬ (B.induce ({1, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 6) (.cons (by decide : B.Adj 6 4) (.cons (by decide : B.Adj 4 5) (.cons (by decide : B.Adj 5 1) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_29 : ¬ (B.induce ({0, 1, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 1) (.cons (by decide : B.Adj 1 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_30 : ¬ (B.induce ({2, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 2 2 := .cons (by decide : B.Adj 2 6) (.cons (by decide : B.Adj 6 4) (.cons (by decide : B.Adj 4 5) (.cons (by decide : B.Adj 5 2) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_31 : ¬ (B.induce ({0, 2, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_32 : ¬ (B.induce ({1, 2, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 1) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_33 : ¬ (B.induce ({0, 1, 2, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_34 : ¬ (B.induce ({3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 3 3 := .cons (by decide : B.Adj 3 5) (.cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 3) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_35 : ¬ (B.induce ({0, 3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 3) (.cons (by decide : B.Adj 3 4) (.cons (by decide : B.Adj 4 0) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_36 : ¬ (B.induce ({1, 3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 5 5 := .cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 5) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_37 : ¬ (B.induce ({0, 1, 3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 1) (.cons (by decide : B.Adj 1 0) (.nil)))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_38 : ¬ (B.induce ({2, 3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 2 2 := .cons (by decide : B.Adj 2 5) (.cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 2) (.nil))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_39 : ¬ (B.induce ({0, 2, 3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 5) (.cons (by decide : B.Adj 5 2) (.cons (by decide : B.Adj 2 3) (.cons (by decide : B.Adj 3 4) (.cons (by decide : B.Adj 4 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_40 : ¬ (B.induce ({1, 2, 3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 1 1 := .cons (by decide : B.Adj 1 5) (.cons (by decide : B.Adj 5 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

lemma b_high_41 : ¬ (B.induce ({0, 1, 2, 3, 4, 5, 6} : Set (Fin 7))).IsAcyclic := by
  let w : B.Walk 0 0 := .cons (by decide : B.Adj 0 4) (.cons (by decide : B.Adj 4 3) (.cons (by decide : B.Adj 3 2) (.cons (by decide : B.Adj 2 1) (.cons (by decide : B.Adj 1 0) (.nil)))))
  have hw : w.IsCycle := by decide
  exact not_isAcyclic_of_cycle w hw (by decide)

end AlbertsonBerman
