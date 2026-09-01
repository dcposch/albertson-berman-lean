import AlbertsonBerman.Cycles
import AlbertsonBerman.ForestBound
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation

/-!
Terminal profile of the icosahedral gadget `X` and the pentagonal-bipyramid
score `β(B,Q)`. Hard cases are the explicit cycles in `Cycles.lean`; every other
candidate contains a triangle, discharged by `testBit` adjacency.
-/

open Finset SimpleGraph AlbertsonBerman

namespace AlbertsonBerman

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Neighbor masks of `X` on `Fin 14`. -/
def xMask : Fin 14 → ℕ := ![126, 965, 1547, 3093, 6185, 4561, 163, 354, 12962, 9478,
  10764, 13336, 10544, 7936]

def xAdjB (i j : Fin 14) : Bool := (xMask i).testBit j.val

/-- Neighbor masks of `B` on `Fin 7`. -/
def bMask : Fin 7 → ℕ := ![114, 101, 106, 116, 105, 31, 31]

def bAdjB (i j : Fin 7) : Bool := (bMask i).testBit j.val

lemma x_mem_iff (i j : Fin 14) :
    s(i, j) ∈ xEdges ∧ i ≠ j ↔ xAdjB i j = true := by
  fin_cases i <;> fin_cases j <;> decide

lemma xAdjB_iff {i j : Fin 14} : X.Adj i j ↔ xAdjB i j = true := by
  rw [X, fromEdgeSet_adj]
  exact x_mem_iff i j

lemma b_mem_iff (i j : Fin 7) :
    s(i, j) ∈ bEdges ∧ i ≠ j ↔ bAdjB i j = true := by
  fin_cases i <;> fin_cases j <;> decide

lemma bAdjB_iff {i j : Fin 7} : B.Adj i j ↔ bAdjB i j = true := by
  rw [B, fromEdgeSet_adj]
  exact b_mem_iff i j

lemma seven_int_cert (s : Finset (Fin 14))
    (h6 : 6 ∉ s) (h7 : 7 ∉ s) (hc : #s = 7) :
    (∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
        a < b ∧ b < c ∧ xAdjB a b = true ∧ xAdjB b c = true ∧ xAdjB c a = true) ∨
      s = {0, 1, 3, 5, 8, 10, 13} ∨
      s = {0, 1, 3, 5, 8, 11, 13} ∨
      s = {0, 1, 3, 5, 9, 10, 12} ∨
      s = {0, 1, 3, 5, 9, 11, 12} ∨
      s = {0, 1, 3, 5, 9, 11, 13} ∨
      s = {0, 1, 3, 5, 9, 12, 13} ∨
      s = {0, 1, 3, 5, 10, 12, 13} ∨
      s = {0, 1, 5, 9, 10, 11, 12} ∨
      s = {1, 2, 3, 4, 5, 8, 13} ∨
      s = {1, 2, 3, 5, 8, 11, 13} ∨
      s = {1, 2, 4, 5, 8, 10, 11} ∨
      s = {1, 2, 4, 5, 8, 10, 13} ∨
      s = {1, 2, 4, 5, 8, 11, 13} ∨
      s = {1, 3, 4, 5, 8, 10, 13} := by
  decide +revert

lemma of_cycle_setX {s : Finset (Fin 14)} {t : Set (Fin 14)}
    (h : ∀ x, x ∈ s ↔ x ∈ t) (ht : ¬ (X.induce t).IsAcyclic) :
    ¬ (X.induce (s : Set (Fin 14))).IsAcyclic := by
  rwa [show (s : Set (Fin 14)) = t from Set.ext h]

lemma of_cycle_setB {s : Finset (Fin 7)} {t : Set (Fin 7)}
    (h : ∀ x, x ∈ s ↔ x ∈ t) (ht : ¬ (B.induce t).IsAcyclic) :
    ¬ (B.induce (s : Set (Fin 7))).IsAcyclic := by
  rwa [show (s : Set (Fin 7)) = t from Set.ext h]

/-- Seven internal vertices of `X` always induce a cycle. -/
lemma seven_int_not_acyclic (s : Finset (Fin 14))
    (h6 : 6 ∉ s) (h7 : 7 ∉ s) (hc : #s = 7) :
    ¬ (X.induce (s : Set (Fin 14))).IsAcyclic := by
  have h := seven_int_cert s h6 h7 hc
  rcases h with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha, b, hb, c, hc, _, _, hab, hbc, hca⟩ := h
    exact not_isAcyclic_of_triangle_in ha hb hc
      (xAdjB_iff.mpr hab) (xAdjB_iff.mpr hbc) (xAdjB_iff.mpr hca)
  · exact of_cycle_setX (fun x => by simp) x_empty_0
  · exact of_cycle_setX (fun x => by simp) x_empty_1
  · exact of_cycle_setX (fun x => by simp) x_empty_2
  · exact of_cycle_setX (fun x => by simp) x_empty_3
  · exact of_cycle_setX (fun x => by simp) x_empty_4
  · exact of_cycle_setX (fun x => by simp) x_empty_5
  · exact of_cycle_setX (fun x => by simp) x_empty_6
  · exact of_cycle_setX (fun x => by simp) x_empty_7
  · exact of_cycle_setX (fun x => by simp) x_empty_8
  · exact of_cycle_setX (fun x => by simp) x_empty_9
  · exact of_cycle_setX (fun x => by simp) x_empty_10
  · exact of_cycle_setX (fun x => by simp) x_empty_11
  · exact of_cycle_setX (fun x => by simp) x_empty_12
  · exact of_cycle_setX (fun x => by simp) x_empty_13

lemma gh_eight_cert (s : Finset (Fin 14))
    (h6 : 6 ∈ s) (h7 : 7 ∈ s) (hc : #s = 8) :
    (∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
        a < b ∧ b < c ∧ xAdjB a b = true ∧ xAdjB b c = true ∧ xAdjB c a = true) ∨
      s = {0, 2, 4, 6, 7, 8, 9, 11} ∨
      s = {0, 2, 4, 6, 7, 8, 9, 12} ∨
      s = {0, 2, 4, 6, 7, 8, 10, 11} ∨
      s = {0, 2, 4, 6, 7, 8, 10, 12} ∨
      s = {0, 2, 4, 6, 7, 8, 10, 13} ∨
      s = {0, 2, 4, 6, 7, 8, 11, 13} ∨
      s = {0, 2, 4, 6, 7, 9, 11, 13} ∨
      s = {0, 2, 4, 6, 7, 9, 12, 13} ∨
      s = {0, 2, 4, 6, 7, 10, 12, 13} ∨
      s = {0, 2, 6, 7, 8, 9, 11, 12} ∨
      s = {0, 2, 6, 7, 8, 10, 11, 12} ∨
      s = {0, 3, 6, 7, 8, 9, 10, 12} ∨
      s = {0, 3, 6, 7, 8, 9, 11, 12} ∨
      s = {0, 4, 6, 7, 8, 9, 10, 11} ∨
      s = {0, 4, 6, 7, 8, 9, 10, 12} ∨
      s = {0, 6, 7, 8, 9, 10, 11, 12} ∨
      s = {2, 3, 4, 6, 7, 8, 9, 12} ∨
      s = {2, 3, 4, 6, 7, 9, 12, 13} ∨
      s = {2, 3, 6, 7, 8, 9, 11, 12} ∨
      s = {3, 4, 6, 7, 8, 9, 10, 12} := by
  decide +revert

/-- Six internal vertices together with both terminals induce a cycle. -/
lemma gh_eight_not_acyclic (s : Finset (Fin 14))
    (h6 : 6 ∈ s) (h7 : 7 ∈ s) (hc : #s = 8) :
    ¬ (X.induce (s : Set (Fin 14))).IsAcyclic := by
  have h := gh_eight_cert s h6 h7 hc
  rcases h with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha, b, hb, c, hc, _, _, hab, hbc, hca⟩ := h
    exact not_isAcyclic_of_triangle_in ha hb hc
      (xAdjB_iff.mpr hab) (xAdjB_iff.mpr hbc) (xAdjB_iff.mpr hca)
  · exact of_cycle_setX (fun x => by simp) x_gh_0
  · exact of_cycle_setX (fun x => by simp) x_gh_1
  · exact of_cycle_setX (fun x => by simp) x_gh_2
  · exact of_cycle_setX (fun x => by simp) x_gh_3
  · exact of_cycle_setX (fun x => by simp) x_gh_4
  · exact of_cycle_setX (fun x => by simp) x_gh_5
  · exact of_cycle_setX (fun x => by simp) x_gh_6
  · exact of_cycle_setX (fun x => by simp) x_gh_7
  · exact of_cycle_setX (fun x => by simp) x_gh_8
  · exact of_cycle_setX (fun x => by simp) x_gh_9
  · exact of_cycle_setX (fun x => by simp) x_gh_10
  · exact of_cycle_setX (fun x => by simp) x_gh_11
  · exact of_cycle_setX (fun x => by simp) x_gh_12
  · exact of_cycle_setX (fun x => by simp) x_gh_13
  · exact of_cycle_setX (fun x => by simp) x_gh_14
  · exact of_cycle_setX (fun x => by simp) x_gh_15
  · exact of_cycle_setX (fun x => by simp) x_gh_16
  · exact of_cycle_setX (fun x => by simp) x_gh_17
  · exact of_cycle_setX (fun x => by simp) x_gh_18
  · exact of_cycle_setX (fun x => by simp) x_gh_19

/-- `φ(S) = |S| - 1_{0,1∈S} - 1_{2,3∈S}`. -/
def phi (s : Finset (Fin 7)) : ℕ :=
  #s - (if 0 ∈ s ∧ 1 ∈ s then 1 else 0) - (if 2 ∈ s ∧ 3 ∈ s then 1 else 0)

lemma b_phi_cert (s : Finset (Fin 7)) (hφ : 4 ≤ phi s) :
    (∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
        a < b ∧ b < c ∧ bAdjB a b = true ∧ bAdjB b c = true ∧ bAdjB c a = true) ∨
      s = {0, 2, 5, 6} ∨
      s = {0, 3, 5, 6} ∨
      s = {1, 3, 5, 6} ∨
      s = {1, 4, 5, 6} ∨
      s = {2, 4, 5, 6} := by
  decide +revert

/-- A bipyramid set of score at least 4 is not a forest. Hence `β(B,Q) ≤ 3`. -/
lemma b_phi_not_acyclic (s : Finset (Fin 7)) (hφ : 4 ≤ phi s) :
    ¬ (B.induce (s : Set (Fin 7))).IsAcyclic := by
  have h := b_phi_cert s hφ
  rcases h with h | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha, b, hb, c, hc, _, _, hab, hbc, hca⟩ := h
    exact not_isAcyclic_of_triangle_in ha hb hc
      (bAdjB_iff.mpr hab) (bAdjB_iff.mpr hbc) (bAdjB_iff.mpr hca)
  · exact of_cycle_setB (fun x => by simp) b_high_18
  · exact of_cycle_setB (fun x => by simp) b_high_21
  · exact of_cycle_setB (fun x => by simp) b_high_22
  · exact of_cycle_setB (fun x => by simp) b_high_28
  · exact of_cycle_setB (fun x => by simp) b_high_30

end AlbertsonBerman
