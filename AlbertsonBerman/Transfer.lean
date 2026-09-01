import AlbertsonBerman.Cycles
import AlbertsonBerman.ForestBound
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation

/-!
Terminal profile of the icosahedral gadget `X` and the pentagonal-bipyramid
score `β(B,Q)`. Hard cases are the explicit cycles in `Cycles.lean`; every other
candidate contains a triangle, discharged by `testBit` adjacency.

The classification lemmas quantify over `Fin 4096` / `Fin 128` bitmasks rather
than `Finset`. `decide +revert` on `Finset (Fin 14)` allocates multiple
gigabytes and is what Palomar OOM-killed after `Cycles`.
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

/-- Popcount of the low `n` bits. -/
def pc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => (if m.testBit n then 1 else 0) + pc n m

/-- Pack internals `{0..5,8..13}` into 12 bits. -/
def pack (m : ℕ) : ℕ := (m &&& 63) ||| ((m >>> 8) <<< 6)

/-- Inverse of `pack` on masks with bits 6 and 7 clear. -/
def unpack (p : ℕ) : ℕ := (p &&& 63) ||| ((p >>> 6) <<< 8)

/-- Restore terminals 6 and 7 after packing six internals. -/
def unpackGH (p : ℕ) : ℕ := unpack p ||| 64 ||| 128

def bit14 (s : Finset (Fin 14)) (i : Fin 14) : ℕ := if i ∈ s then 2 ^ i.val else 0

def maskOf (s : Finset (Fin 14)) : ℕ :=
  bit14 s 0 ||| bit14 s 1 ||| bit14 s 2 ||| bit14 s 3 ||| bit14 s 4 |||
    bit14 s 5 ||| bit14 s 6 ||| bit14 s 7 ||| bit14 s 8 ||| bit14 s 9 |||
    bit14 s 10 ||| bit14 s 11 ||| bit14 s 12 ||| bit14 s 13

def bit7 (s : Finset (Fin 7)) (i : Fin 7) : ℕ := if i ∈ s then 2 ^ i.val else 0

def maskB (s : Finset (Fin 7)) : ℕ :=
  bit7 s 0 ||| bit7 s 1 ||| bit7 s 2 ||| bit7 s 3 ||| bit7 s 4 ||| bit7 s 5 ||| bit7 s 6

def xTriangles : List (Fin 14 × Fin 14 × Fin 14) :=
  [(0, 1, 2), (0, 1, 6), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 5, 6),
   (1, 2, 9), (1, 6, 7), (1, 7, 8), (1, 8, 9), (2, 3, 10), (2, 9, 10),
   (3, 4, 11), (3, 10, 11), (4, 5, 12), (4, 11, 12), (5, 6, 7), (5, 7, 8),
   (5, 8, 12), (8, 9, 13), (8, 12, 13), (9, 10, 13), (10, 11, 13), (11, 12, 13)]

def bTriangles : List (Fin 7 × Fin 7 × Fin 7) :=
  [(0, 1, 5), (0, 1, 6), (0, 4, 5), (0, 4, 6), (1, 2, 5), (1, 2, 6),
   (2, 3, 5), (2, 3, 6), (3, 4, 5), (3, 4, 6)]

def xTri (m : ℕ) : Bool :=
  xTriangles.any fun t =>
    m.testBit t.1.val && m.testBit t.2.1.val && m.testBit t.2.2.val

def bTri (m : ℕ) : Bool :=
  bTriangles.any fun t =>
    m.testBit t.1.val && m.testBit t.2.1.val && m.testBit t.2.2.val

def phiN (m : ℕ) : ℕ :=
  pc 7 m - (if m.testBit 0 && m.testBit 1 then 1 else 0) -
    (if m.testBit 2 && m.testBit 3 then 1 else 0)

lemma testBit_bit14 (s : Finset (Fin 14)) (i j : Fin 14) :
    (bit14 s j).testBit i.val = true ↔ j ∈ s ∧ i = j := by
  unfold bit14
  split_ifs with hj
  · rw [Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨hj, Fin.eq_of_val_eq h.symm⟩
    · rintro ⟨_, rfl⟩
      rfl
  · simp [hj]

lemma testBit_maskOf (s : Finset (Fin 14)) (i : Fin 14) :
    (maskOf s).testBit i.val = true ↔ i ∈ s := by
  simp only [maskOf, Nat.testBit_or, Bool.or_eq_true, testBit_bit14]
  fin_cases i <;> simp

lemma maskOf_lt (s : Finset (Fin 14)) : maskOf s < 16384 := by
  change maskOf s < 2 ^ 14
  refine Nat.lt_pow_two_of_testBit (n := 14) _ ?_
  intro k hk
  have hbit : ∀ j : Fin 14, (bit14 s j).testBit k = false := by
    intro j
    unfold bit14
    split_ifs
    · exact Nat.testBit_two_pow_of_ne (by omega)
    · simp
  simp [maskOf, Nat.testBit_or, hbit]

lemma testBit_bit7 (s : Finset (Fin 7)) (i j : Fin 7) :
    (bit7 s j).testBit i.val = true ↔ j ∈ s ∧ i = j := by
  unfold bit7
  split_ifs with hj
  · rw [Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨hj, Fin.eq_of_val_eq h.symm⟩
    · rintro ⟨_, rfl⟩
      rfl
  · simp [hj]

lemma testBit_maskB (s : Finset (Fin 7)) (i : Fin 7) :
    (maskB s).testBit i.val = true ↔ i ∈ s := by
  simp only [maskB, Nat.testBit_or, Bool.or_eq_true, testBit_bit7]
  fin_cases i <;> simp

lemma maskB_lt (s : Finset (Fin 7)) : maskB s < 128 := by
  change maskB s < 2 ^ 7
  refine Nat.lt_pow_two_of_testBit (n := 7) _ ?_
  intro k hk
  have hbit : ∀ j : Fin 7, (bit7 s j).testBit k = false := by
    intro j
    unfold bit7
    split_ifs
    · exact Nat.testBit_two_pow_of_ne (by omega)
    · simp
  simp [maskB, Nat.testBit_or, hbit]

lemma eq_of_mask14 (s t : Finset (Fin 14)) (h : maskOf s = maskOf t) : s = t := by
  ext i
  rw [← testBit_maskOf, ← testBit_maskOf, h]

lemma eq_of_maskB (s t : Finset (Fin 7)) (h : maskB s = maskB t) : s = t := by
  ext i
  rw [← testBit_maskB, ← testBit_maskB, h]

lemma testBit_false_of_not_mem14 (s : Finset (Fin 14)) {i : Fin 14} (h : i ∉ s) :
    (maskOf s).testBit i.val = false := by
  cases hb : (maskOf s).testBit i.val
  · rfl
  · exact (h ((testBit_maskOf s i).mp hb)).elim

lemma testBit_false_of_not_mem7 (s : Finset (Fin 7)) {i : Fin 7} (h : i ∉ s) :
    (maskB s).testBit i.val = false := by
  cases hb : (maskB s).testBit i.val
  · rfl
  · exact (h ((testBit_maskB s i).mp hb)).elim

lemma pc_prefix14 (n : ℕ) (hn : n ≤ 14) (s : Finset (Fin 14)) :
    pc n (maskOf s) = #(s.filter fun i => i.val < n) := by
  induction n with
  | zero => simp [pc]
  | succ n ih =>
      have hn' : n ≤ 14 := Nat.le_of_succ_le hn
      have nlt : n < 14 := Nat.lt_of_succ_le hn
      rw [pc, ih hn']
      by_cases hmem : (⟨n, nlt⟩ : Fin 14) ∈ s
      · have hbit : (maskOf s).testBit n = true := (testBit_maskOf s ⟨n, nlt⟩).mpr hmem
        have hinsert :
            s.filter (fun i => i.val < n + 1) =
              insert ⟨n, nlt⟩ (s.filter fun i => i.val < n) := by
          ext i
          simp only [mem_filter, mem_insert, Nat.lt_succ_iff]
          constructor
          · intro ⟨hi, hle⟩
            rcases Nat.lt_or_eq_of_le hle with hlt | heq
            · exact .inr ⟨hi, hlt⟩
            · left
              exact Fin.eq_of_val_eq heq
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hmem, Nat.le_refl _⟩
            · exact ⟨hi, Nat.le_of_lt hlt⟩
        have hnew : (⟨n, nlt⟩ : Fin 14) ∉ s.filter fun i => i.val < n := by
          simp
        rw [hbit, if_pos rfl, hinsert, card_insert_of_notMem hnew, Nat.add_comm]
      · have hbit : (maskOf s).testBit n = false :=
          testBit_false_of_not_mem14 s hmem
        have hsame :
            s.filter (fun i => i.val < n + 1) = s.filter fun i => i.val < n := by
          ext i
          simp only [mem_filter, Nat.lt_succ_iff]
          constructor
          · intro ⟨hi, hle⟩
            refine ⟨hi, ?_⟩
            rcases Nat.lt_or_eq_of_le hle with hlt | heq
            · exact hlt
            · have : i = ⟨n, nlt⟩ := Fin.eq_of_val_eq heq
              subst this
              exact (hmem hi).elim
          · intro ⟨hi, hlt⟩
            exact ⟨hi, Nat.le_of_lt hlt⟩
        rw [hbit, if_neg Bool.false_ne_true, hsame, Nat.zero_add]

lemma pc_prefix7 (n : ℕ) (hn : n ≤ 7) (s : Finset (Fin 7)) :
    pc n (maskB s) = #(s.filter fun i => i.val < n) := by
  induction n with
  | zero => simp [pc]
  | succ n ih =>
      have hn' : n ≤ 7 := Nat.le_of_succ_le hn
      have nlt : n < 7 := Nat.lt_of_succ_le hn
      rw [pc, ih hn']
      by_cases hmem : (⟨n, nlt⟩ : Fin 7) ∈ s
      · have hbit : (maskB s).testBit n = true := (testBit_maskB s ⟨n, nlt⟩).mpr hmem
        have hinsert :
            s.filter (fun i => i.val < n + 1) =
              insert ⟨n, nlt⟩ (s.filter fun i => i.val < n) := by
          ext i
          simp only [mem_filter, mem_insert, Nat.lt_succ_iff]
          constructor
          · intro ⟨hi, hle⟩
            rcases Nat.lt_or_eq_of_le hle with hlt | heq
            · exact .inr ⟨hi, hlt⟩
            · left
              exact Fin.eq_of_val_eq heq
          · rintro (rfl | ⟨hi, hlt⟩)
            · exact ⟨hmem, Nat.le_refl _⟩
            · exact ⟨hi, Nat.le_of_lt hlt⟩
        have hnew : (⟨n, nlt⟩ : Fin 7) ∉ s.filter fun i => i.val < n := by
          simp
        rw [hbit, if_pos rfl, hinsert, card_insert_of_notMem hnew, Nat.add_comm]
      · have hbit : (maskB s).testBit n = false :=
          testBit_false_of_not_mem7 s hmem
        have hsame :
            s.filter (fun i => i.val < n + 1) = s.filter fun i => i.val < n := by
          ext i
          simp only [mem_filter, Nat.lt_succ_iff]
          constructor
          · intro ⟨hi, hle⟩
            refine ⟨hi, ?_⟩
            rcases Nat.lt_or_eq_of_le hle with hlt | heq
            · exact hlt
            · have : i = ⟨n, nlt⟩ := Fin.eq_of_val_eq heq
              subst this
              exact (hmem hi).elim
          · intro ⟨hi, hlt⟩
            exact ⟨hi, Nat.le_of_lt hlt⟩
        rw [hbit, if_neg Bool.false_ne_true, hsame, Nat.zero_add]

lemma pc_maskOf (s : Finset (Fin 14)) : pc 14 (maskOf s) = #s := by
  simpa using pc_prefix14 14 (by decide) s

lemma pc_maskB (s : Finset (Fin 7)) : pc 7 (maskB s) = #s := by
  simpa using pc_prefix7 7 (by decide) s

lemma pack_lt (m : Fin 16384) : pack m.val < 4096 := by
  unfold pack
  have h1 : m.val &&& 63 < 2 ^ 6 :=
    Nat.and_lt_two_pow _ (by decide : (63 : ℕ) < 2 ^ 6)
  have hs : m.val >>> 8 < 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr m.isLt
  have h2 : (m.val >>> 8) <<< 6 < 2 ^ 12 := by
    rw [Nat.shiftLeft_eq]
    have : (m.val >>> 8) * 2 ^ 6 < 64 * 64 :=
      Nat.mul_lt_mul_of_pos_right hs (by decide)
    omega
  have h1' : m.val &&& 63 < 2 ^ 12 := Nat.lt_trans h1 (by decide)
  exact Nat.or_lt_two_pow h1' h2

lemma testBit_pack (m j : ℕ) :
    (pack m).testBit j =
      ((m.testBit j && decide (j < 6)) || (decide (6 ≤ j) && m.testBit (j + 2))) := by
  unfold pack
  have h63 : (63 : ℕ).testBit j = decide (j < 6) := by
    have : (63 : ℕ) = 2 ^ 6 - 1 := by decide
    rw [this, Nat.testBit_two_pow_sub_one]
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, h63]
  by_cases h : j < 6
  · simp [h, Nat.not_le_of_gt h]
  · have hge : 6 ≤ j := Nat.le_of_not_lt h
    have : 8 + (j - 6) = j + 2 := by omega
    simp [h, hge, this]

lemma testBit_unpack (p j : ℕ) :
    (unpack p).testBit j =
      ((p.testBit j && decide (j < 6)) || (decide (8 ≤ j) && p.testBit (j - 2))) := by
  unfold unpack
  have h63 : (63 : ℕ).testBit j = decide (j < 6) := by
    have : (63 : ℕ) = 2 ^ 6 - 1 := by decide
    rw [this, Nat.testBit_two_pow_sub_one]
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, h63]
  by_cases h : 8 ≤ j
  · have heq : 6 + (j - 8) = j - 2 := by omega
    simp [h, heq]
  · simp [h]

lemma unpack_lt (p : ℕ) (hp : p < 4096) : unpack p < 16384 := by
  unfold unpack
  have h1 : p &&& 63 < 2 ^ 6 :=
    Nat.and_lt_two_pow _ (by decide : (63 : ℕ) < 2 ^ 6)
  have hs : p >>> 6 < 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 64)).mpr (Nat.lt_of_lt_of_le hp (by decide))
  have h2 : (p >>> 6) <<< 8 < 2 ^ 14 := by
    rw [Nat.shiftLeft_eq]
    have : (p >>> 6) * 2 ^ 8 < 64 * 256 :=
      Nat.mul_lt_mul_of_pos_right hs (by decide)
    omega
  have h1' : p &&& 63 < 2 ^ 14 := Nat.lt_trans h1 (by decide)
  exact Nat.or_lt_two_pow h1' h2

lemma unpack_pack_clean (m : Fin 16384)
    (h6 : m.val.testBit 6 = false) (h7 : m.val.testBit 7 = false) :
    unpack (pack m.val) = m.val := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hm : m.val < 2 ^ 14 := m.isLt
  by_cases hj : 14 ≤ j
  · have hmbit : m.val.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right Nat.zero_lt_two hj))
    have hup : unpack (pack m.val) < 2 ^ 14 := unpack_lt _ (pack_lt m)
    have hubit : (unpack (pack m.val)).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hup (Nat.pow_le_pow_right Nat.zero_lt_two hj))
    simp [hmbit, hubit]
  · have hj' : j < 14 := Nat.lt_of_not_ge hj
    have hu := testBit_unpack (pack m.val) j
    have hp := testBit_pack m.val j
    rw [hu, hp]
    rcases Nat.lt_or_ge j 6 with hlt6 | hge6
    · simp [hlt6, Nat.not_le_of_gt (Nat.lt_trans hlt6 (by decide : (6 : ℕ) < 8))]
    · rcases Nat.lt_or_ge j 8 with hlt8 | hge8
      · have : j = 6 ∨ j = 7 := by omega
        rcases this with rfl | rfl <;> simp [h6, h7, hge6]
      · have : ¬ j < 6 := Nat.not_lt_of_ge hge6
        have hj2 : j - 2 + 2 = j := by omega
        have hp' := testBit_pack m.val (j - 2)
        have hlt : ¬ j - 2 < 6 := by omega
        have hle : 6 ≤ j - 2 := by omega
        rw [hp']
        simp [hge8, hge6, this, hj2, hlt, hle]

lemma pc_unfold_add (n m : ℕ) :
    pc (n + 1) m = pc n m + if m.testBit n then 1 else 0 := by
  rw [pc, Nat.add_comm]

lemma pc_pack_clean (m : Fin 16384)
    (h6 : m.val.testBit 6 = false) (h7 : m.val.testBit 7 = false) :
    pc 12 (pack m.val) = pc 14 m.val := by
  have b0 := testBit_pack m.val 0
  have b1 := testBit_pack m.val 1
  have b2 := testBit_pack m.val 2
  have b3 := testBit_pack m.val 3
  have b4 := testBit_pack m.val 4
  have b5 := testBit_pack m.val 5
  have b6 := testBit_pack m.val 6
  have b7 := testBit_pack m.val 7
  have b8 := testBit_pack m.val 8
  have b9 := testBit_pack m.val 9
  have b10 := testBit_pack m.val 10
  have b11 := testBit_pack m.val 11
  have b12 := testBit_pack m.val 12
  have b13 := testBit_pack m.val 13
  simp [pc, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, h6, h7]

lemma testBit_unpackGH (p j : ℕ) :
    (unpackGH p).testBit j =
      ((unpack p).testBit j || decide (j = 6) || decide (j = 7)) := by
  unfold unpackGH
  have h64 : (64 : ℕ).testBit j = decide (j = 6) := by
    have : (64 : ℕ) = 2 ^ 6 := by decide
    rw [this, Nat.testBit_two_pow]
    simp [eq_comm]
  have h128 : (128 : ℕ).testBit j = decide (j = 7) := by
    have : (128 : ℕ) = 2 ^ 7 := by decide
    rw [this, Nat.testBit_two_pow]
    simp [eq_comm]
  simp only [Nat.testBit_or, h64, h128]

lemma unpackGH_pack (m : Fin 16384)
    (h6 : m.val.testBit 6 = true) (h7 : m.val.testBit 7 = true) :
    unpackGH (pack m.val) = m.val := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hm : m.val < 2 ^ 14 := m.isLt
  by_cases hj : 14 ≤ j
  · have hmbit : m.val.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right Nat.zero_lt_two hj))
    have : unpackGH (pack m.val) < 2 ^ 14 := by
      unfold unpackGH
      have : unpack (pack m.val) < 2 ^ 14 := unpack_lt _ (pack_lt m)
      have h64 : (64 : ℕ) < 2 ^ 14 := by decide
      have h128 : (128 : ℕ) < 2 ^ 14 := by decide
      exact Nat.or_lt_two_pow (Nat.or_lt_two_pow this h64) h128
    have hubit : (unpackGH (pack m.val)).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le this (Nat.pow_le_pow_right Nat.zero_lt_two hj))
    simp [hmbit, hubit]
  · have hj' : j < 14 := Nat.lt_of_not_ge hj
    have hg := testBit_unpackGH (pack m.val) j
    have hu := testBit_unpack (pack m.val) j
    have hp := testBit_pack m.val j
    rw [hg, hu, hp]
    rcases Nat.lt_or_ge j 6 with hlt6 | hge6
    · simp [hlt6, Nat.not_le_of_gt (Nat.lt_trans hlt6 (by decide : (6 : ℕ) < 8)),
        Nat.ne_of_lt hlt6, Nat.ne_of_lt (Nat.lt_trans hlt6 (by decide : (6 : ℕ) < 7))]
    · rcases Nat.lt_or_ge j 8 with hlt8 | hge8
      · have : j = 6 ∨ j = 7 := by omega
        rcases this with rfl | rfl <;> simp [h6, h7, hge6]
      · have : ¬ j < 6 := Nat.not_lt_of_ge hge6
        have hj2 : j - 2 + 2 = j := by omega
        have n6 : j ≠ 6 := by omega
        have n7 : j ≠ 7 := by omega
        have hp' := testBit_pack m.val (j - 2)
        have hlt : ¬ j - 2 < 6 := by omega
        have hle : 6 ≤ j - 2 := by omega
        rw [hp']
        simp [hge8, hge6, this, hj2, n6, n7, hlt, hle]

lemma pc_pack_gh (m : Fin 16384)
    (h6 : m.val.testBit 6 = true) (h7 : m.val.testBit 7 = true) :
    pc 12 (pack m.val) + 2 = pc 14 m.val := by
  have b0 := testBit_pack m.val 0
  have b1 := testBit_pack m.val 1
  have b2 := testBit_pack m.val 2
  have b3 := testBit_pack m.val 3
  have b4 := testBit_pack m.val 4
  have b5 := testBit_pack m.val 5
  have b6 := testBit_pack m.val 6
  have b7 := testBit_pack m.val 7
  have b8 := testBit_pack m.val 8
  have b9 := testBit_pack m.val 9
  have b10 := testBit_pack m.val 10
  have b11 := testBit_pack m.val 11
  have b12 := testBit_pack m.val 12
  have b13 := testBit_pack m.val 13
  simp [pc, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, h6, h7]
  omega

lemma mem_xTriangles {a b c : Fin 14} (h : (a, b, c) ∈ xTriangles) :
    a < b ∧ b < c ∧ xAdjB a b = true ∧ xAdjB b c = true ∧ xAdjB c a = true := by
  have : (a, b, c) = (0, 1, 2) ∨ (a, b, c) = (0, 1, 6) ∨ (a, b, c) = (0, 2, 3) ∨
      (a, b, c) = (0, 3, 4) ∨ (a, b, c) = (0, 4, 5) ∨ (a, b, c) = (0, 5, 6) ∨
      (a, b, c) = (1, 2, 9) ∨ (a, b, c) = (1, 6, 7) ∨ (a, b, c) = (1, 7, 8) ∨
      (a, b, c) = (1, 8, 9) ∨ (a, b, c) = (2, 3, 10) ∨ (a, b, c) = (2, 9, 10) ∨
      (a, b, c) = (3, 4, 11) ∨ (a, b, c) = (3, 10, 11) ∨ (a, b, c) = (4, 5, 12) ∨
      (a, b, c) = (4, 11, 12) ∨ (a, b, c) = (5, 6, 7) ∨ (a, b, c) = (5, 7, 8) ∨
      (a, b, c) = (5, 8, 12) ∨ (a, b, c) = (8, 9, 13) ∨ (a, b, c) = (8, 12, 13) ∨
      (a, b, c) = (9, 10, 13) ∨ (a, b, c) = (10, 11, 13) ∨ (a, b, c) = (11, 12, 13) := by
    simpa [xTriangles] using h
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    injection h with h1 h2
    injection h2 with h2 h3
    subst h1; subst h2; subst h3
    decide

lemma mem_bTriangles {a b c : Fin 7} (h : (a, b, c) ∈ bTriangles) :
    a < b ∧ b < c ∧ bAdjB a b = true ∧ bAdjB b c = true ∧ bAdjB c a = true := by
  have : (a, b, c) = (0, 1, 5) ∨ (a, b, c) = (0, 1, 6) ∨ (a, b, c) = (0, 4, 5) ∨
      (a, b, c) = (0, 4, 6) ∨ (a, b, c) = (1, 2, 5) ∨ (a, b, c) = (1, 2, 6) ∨
      (a, b, c) = (2, 3, 5) ∨ (a, b, c) = (2, 3, 6) ∨ (a, b, c) = (3, 4, 5) ∨
      (a, b, c) = (3, 4, 6) := by
    simpa [bTriangles] using h
  rcases this with h | h | h | h | h | h | h | h | h | h
  all_goals
    injection h with h1 h2
    injection h2 with h2 h3
    subst h1; subst h2; subst h3
    decide

lemma xTri_elim {m : ℕ} (h : xTri m = true) :
    ∃ a b c : Fin 14, a < b ∧ b < c ∧
      m.testBit a.val = true ∧ m.testBit b.val = true ∧ m.testBit c.val = true ∧
      xAdjB a b = true ∧ xAdjB b c = true ∧ xAdjB c a = true := by
  obtain ⟨t, ht, hb⟩ := List.any_eq_true.mp h
  rcases t with ⟨a, b, c⟩
  have hbits : (m.testBit a.val = true ∧ m.testBit b.val = true) ∧ m.testBit c.val = true := by
    simpa [Bool.and_eq_true] using hb
  have hadj := mem_xTriangles ht
  exact ⟨a, b, c, hadj.1, hadj.2.1, hbits.1.1, hbits.1.2, hbits.2, hadj.2.2.1, hadj.2.2.2.1,
    hadj.2.2.2.2⟩

lemma bTri_elim {m : ℕ} (h : bTri m = true) :
    ∃ a b c : Fin 7, a < b ∧ b < c ∧
      m.testBit a.val = true ∧ m.testBit b.val = true ∧ m.testBit c.val = true ∧
      bAdjB a b = true ∧ bAdjB b c = true ∧ bAdjB c a = true := by
  obtain ⟨t, ht, hb⟩ := List.any_eq_true.mp h
  rcases t with ⟨a, b, c⟩
  have hbits : (m.testBit a.val = true ∧ m.testBit b.val = true) ∧ m.testBit c.val = true := by
    simpa [Bool.and_eq_true] using hb
  have hadj := mem_bTriangles ht
  exact ⟨a, b, c, hadj.1, hadj.2.1, hbits.1.1, hbits.1.2, hbits.2, hadj.2.2.1, hadj.2.2.2.1,
    hadj.2.2.2.2⟩

def class7 (p : ℕ) : Bool :=
  decide
    (pc 12 p ≠ 7 ∨ xTri (unpack p) = true ∨
      unpack p = 9515 ∨ unpack p = 10539 ∨ unpack p = 5675 ∨
      unpack p = 6699 ∨ unpack p = 10795 ∨ unpack p = 12843 ∨
      unpack p = 13355 ∨ unpack p = 7715 ∨ unpack p = 8510 ∨
      unpack p = 10542 ∨ unpack p = 3382 ∨ unpack p = 9526 ∨
      unpack p = 10550 ∨ unpack p = 9530)

def classGH (p : ℕ) : Bool :=
  decide
    (pc 12 p ≠ 6 ∨ xTri (unpackGH p) = true ∨
      unpackGH p = 3029 ∨ unpackGH p = 5077 ∨ unpackGH p = 3541 ∨
      unpackGH p = 5589 ∨ unpackGH p = 9685 ∨ unpackGH p = 10709 ∨
      unpackGH p = 10965 ∨ unpackGH p = 13013 ∨ unpackGH p = 13525 ∨
      unpackGH p = 7109 ∨ unpackGH p = 7621 ∨ unpackGH p = 6089 ∨
      unpackGH p = 7113 ∨ unpackGH p = 4049 ∨ unpackGH p = 6097 ∨
      unpackGH p = 8129 ∨ unpackGH p = 5084 ∨ unpackGH p = 13020 ∨
      unpackGH p = 7116 ∨ unpackGH p = 6104)

def classB (m : ℕ) : Bool :=
  decide
    (phiN m < 4 ∨ bTri m = true ∨
      m = 101 ∨ m = 105 ∨ m = 106 ∨ m = 114 ∨ m = 116)

def allClass (c : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => c n && allClass c n

lemma allClass_lt (c : ℕ → Bool) :
    ∀ n, allClass c n = true → ∀ p, p < n → c p = true := by
  intro n
  induction n with
  | zero =>
      intro _ p hp
      exact (Nat.not_lt_zero p hp).elim
  | succ n ih =>
      intro h p hp
      have hc : c n = true ∧ allClass c n = true := by
        simpa [allClass, Bool.and_eq_true] using h
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hp) with hlt | rfl
      · exact ih hc.2 p hlt
      · exact hc.1

lemma seven_packed (p : Fin 4096) (hpc : pc 12 p.val = 7) :
    xTri (unpack p.val) = true ∨
      unpack p.val = 9515 ∨ unpack p.val = 10539 ∨ unpack p.val = 5675 ∨
        unpack p.val = 6699 ∨ unpack p.val = 10795 ∨ unpack p.val = 12843 ∨
          unpack p.val = 13355 ∨ unpack p.val = 7715 ∨ unpack p.val = 8510 ∨
            unpack p.val = 10542 ∨ unpack p.val = 3382 ∨ unpack p.val = 9526 ∨
              unpack p.val = 10550 ∨ unpack p.val = 9530 := by
  have hok : allClass class7 4096 = true := by decide
  have hc : class7 p.val = true := allClass_lt class7 4096 hok p.val p.isLt
  have hprop := decide_eq_true_eq.mp hc
  simpa [hpc] using hprop

lemma gh_packed (p : Fin 4096) (hpc : pc 12 p.val = 6) :
    xTri (unpackGH p.val) = true ∨
      unpackGH p.val = 3029 ∨ unpackGH p.val = 5077 ∨ unpackGH p.val = 3541 ∨
        unpackGH p.val = 5589 ∨ unpackGH p.val = 9685 ∨ unpackGH p.val = 10709 ∨
          unpackGH p.val = 10965 ∨ unpackGH p.val = 13013 ∨ unpackGH p.val = 13525 ∨
            unpackGH p.val = 7109 ∨ unpackGH p.val = 7621 ∨ unpackGH p.val = 6089 ∨
              unpackGH p.val = 7113 ∨ unpackGH p.val = 4049 ∨ unpackGH p.val = 6097 ∨
                unpackGH p.val = 8129 ∨ unpackGH p.val = 5084 ∨ unpackGH p.val = 13020 ∨
                  unpackGH p.val = 7116 ∨ unpackGH p.val = 6104 := by
  have hok : allClass classGH 4096 = true := by decide
  have hc : classGH p.val = true := allClass_lt classGH 4096 hok p.val p.isLt
  have hprop := decide_eq_true_eq.mp hc
  simpa [hpc] using hprop

lemma b_packed (m : Fin 128) (hφ : 4 ≤ phiN m.val) :
    bTri m.val = true ∨
      m.val = 101 ∨ m.val = 105 ∨ m.val = 106 ∨ m.val = 114 ∨ m.val = 116 := by
  have hok : allClass classB 128 = true := by decide
  have hc : classB m.val = true := allClass_lt classB 128 hok m.val m.isLt
  have hprop := decide_eq_true_eq.mp hc
  have : ¬ phiN m.val < 4 := Nat.not_lt.mpr hφ
  simpa [this] using hprop

lemma eqLit14 (s t : Finset (Fin 14)) {n : ℕ}
    (hs : maskOf s = n) (ht : maskOf t = n) : s = t :=
  eq_of_mask14 s t (hs.trans ht.symm)

lemma eqLit7 (s t : Finset (Fin 7)) {n : ℕ}
    (hs : maskB s = n) (ht : maskB t = n) : s = t :=
  eq_of_maskB s t (hs.trans ht.symm)

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
  let m : Fin 16384 := ⟨maskOf s, maskOf_lt s⟩
  have h6b : m.val.testBit 6 = false := testBit_false_of_not_mem14 s h6
  have h7b : m.val.testBit 7 = false := testBit_false_of_not_mem14 s h7
  let p : Fin 4096 := ⟨pack m.val, pack_lt m⟩
  have hpc : pc 12 p.val = 7 := by
    change pc 12 (pack m.val) = 7
    have h1 := pc_pack_clean m h6b h7b
    have h2 := pc_maskOf s
    rw [h1, show m.val = maskOf s from rfl, h2, hc]
  have hunp : unpack p.val = m.val := unpack_pack_clean m h6b h7b
  have h := seven_packed p hpc
  rw [hunp] at h
  have mem {i : Fin 14} : i ∈ s ↔ (maskOf s).testBit i.val = true :=
    (testBit_maskOf s i).symm
  rcases h with htri | h0 | h1 | h2 | h3 | h4 | h5 | h6' | h7' | h8 | h9 | h10 | h11 | h12 | h13
  · left
    obtain ⟨a, b, c, hab, hbc, ha, hb, hc', eab, ebc, eca⟩ := xTri_elim htri
    exact ⟨a, mem.2 ha, b, mem.2 hb, c, mem.2 hc', hab, hbc, eab, ebc, eca⟩
  · exact .inr <| .inl <| eqLit14 s {0, 1, 3, 5, 8, 10, 13} h0 (by decide)
  · exact .inr <| .inr <| .inl <| eqLit14 s {0, 1, 3, 5, 8, 11, 13} h1 (by decide)
  · exact .inr <| .inr <| .inr <| .inl <| eqLit14 s {0, 1, 3, 5, 9, 10, 12} h2 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 1, 3, 5, 9, 11, 12} h3 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 1, 3, 5, 9, 11, 13} h4 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 1, 3, 5, 9, 12, 13} h5 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 1, 3, 5, 10, 12, 13} h6' (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 1, 5, 9, 10, 11, 12} h7' (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {1, 2, 3, 4, 5, 8, 13} h8 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {1, 2, 3, 5, 8, 11, 13} h9 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inl <| eqLit14 s {1, 2, 4, 5, 8, 10, 11} h10 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inl <| eqLit14 s {1, 2, 4, 5, 8, 10, 13} h11 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inl <| eqLit14 s {1, 2, 4, 5, 8, 11, 13} h12 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| eqLit14 s {1, 3, 4, 5, 8, 10, 13} h13 (by decide)

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
  let m : Fin 16384 := ⟨maskOf s, maskOf_lt s⟩
  have h6b : m.val.testBit 6 = true := (testBit_maskOf s 6).mpr h6
  have h7b : m.val.testBit 7 = true := (testBit_maskOf s 7).mpr h7
  let p : Fin 4096 := ⟨pack m.val, pack_lt m⟩
  have hpc : pc 12 p.val = 6 := by
    change pc 12 (pack m.val) = 6
    have h1 := pc_pack_gh m h6b h7b
    have h2 := pc_maskOf s
    have : pc 12 (pack m.val) + 2 = 8 := by
      rw [h1, show m.val = maskOf s from rfl, h2, hc]
    omega
  have hunp : unpackGH p.val = m.val := unpackGH_pack m h6b h7b
  have h := gh_packed p hpc
  rw [hunp] at h
  have mem {i : Fin 14} : i ∈ s ↔ (maskOf s).testBit i.val = true :=
    (testBit_maskOf s i).symm
  rcases h with
    htri | h0 | h1 | h2 | h3 | h4 | h5 | h6' | h7' | h8 | h9 | h10 | h11 | h12 | h13 |
      h14 | h15 | h16 | h17 | h18 | h19
  · left
    obtain ⟨a, b, c, hab, hbc, ha, hb, hc', eab, ebc, eca⟩ := xTri_elim htri
    exact ⟨a, mem.2 ha, b, mem.2 hb, c, mem.2 hc', hab, hbc, eab, ebc, eca⟩
  · exact .inr <| .inl <| eqLit14 s {0, 2, 4, 6, 7, 8, 9, 11} h0 (by decide)
  · exact .inr <| .inr <| .inl <| eqLit14 s {0, 2, 4, 6, 7, 8, 9, 12} h1 (by decide)
  · exact .inr <| .inr <| .inr <| .inl <| eqLit14 s {0, 2, 4, 6, 7, 8, 10, 11} h2 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 2, 4, 6, 7, 8, 10, 12} h3 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 2, 4, 6, 7, 8, 10, 13} h4 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 2, 4, 6, 7, 8, 11, 13} h5 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 2, 4, 6, 7, 9, 11, 13} h6' (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 2, 4, 6, 7, 9, 12, 13} h7' (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 2, 4, 6, 7, 10, 12, 13} h8 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 2, 6, 7, 8, 9, 11, 12} h9 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inl <| eqLit14 s {0, 2, 6, 7, 8, 10, 11, 12} h10 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inl <| eqLit14 s {0, 3, 6, 7, 8, 9, 10, 12} h11 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inl <| eqLit14 s {0, 3, 6, 7, 8, 9, 11, 12} h12 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| .inl <| eqLit14 s {0, 4, 6, 7, 8, 9, 10, 11} h13 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| .inr <| .inl <| eqLit14 s {0, 4, 6, 7, 8, 9, 10, 12} h14 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {0, 6, 7, 8, 9, 10, 11, 12} h15 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {2, 3, 4, 6, 7, 8, 9, 12} h16 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {2, 3, 4, 6, 7, 9, 12, 13} h17 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <|
      eqLit14 s {2, 3, 6, 7, 8, 9, 11, 12} h18 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <|
      eqLit14 s {3, 4, 6, 7, 8, 9, 10, 12} h19 (by decide)

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

lemma phi_maskB (s : Finset (Fin 7)) : phi s = phiN (maskB s) := by
  simp only [phi, phiN, pc_maskB]
  cases h0 : decide ((0 : Fin 7) ∈ s) <;> cases h1 : decide ((1 : Fin 7) ∈ s) <;>
    cases h2 : decide ((2 : Fin 7) ∈ s) <;> cases h3 : decide ((3 : Fin 7) ∈ s)
  all_goals
    have := testBit_maskB s (0 : Fin 7)
    have := testBit_maskB s (1 : Fin 7)
    have := testBit_maskB s (2 : Fin 7)
    have := testBit_maskB s (3 : Fin 7)
    simp_all [Bool.and_eq_true]

lemma b_phi_cert (s : Finset (Fin 7)) (hφ : 4 ≤ phi s) :
    (∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s,
        a < b ∧ b < c ∧ bAdjB a b = true ∧ bAdjB b c = true ∧ bAdjB c a = true) ∨
      s = {0, 2, 5, 6} ∨
      s = {0, 3, 5, 6} ∨
      s = {1, 3, 5, 6} ∨
      s = {1, 4, 5, 6} ∨
      s = {2, 4, 5, 6} := by
  let m : Fin 128 := ⟨maskB s, maskB_lt s⟩
  have hφ' : 4 ≤ phiN m.val := by
    simpa [phi_maskB] using hφ
  have h := b_packed m hφ'
  have mem {i : Fin 7} : i ∈ s ↔ (maskB s).testBit i.val = true :=
    (testBit_maskB s i).symm
  rcases h with htri | h0 | h1 | h2 | h3 | h4
  · left
    obtain ⟨a, b, c, hab, hbc, ha, hb, hc', eab, ebc, eca⟩ := bTri_elim htri
    exact ⟨a, mem.2 ha, b, mem.2 hb, c, mem.2 hc', hab, hbc, eab, ebc, eca⟩
  · exact .inr <| .inl <| eqLit7 s {0, 2, 5, 6} h0 (by decide)
  · exact .inr <| .inr <| .inl <| eqLit7 s {0, 3, 5, 6} h1 (by decide)
  · exact .inr <| .inr <| .inr <| .inl <| eqLit7 s {1, 3, 5, 6} h2 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inl <| eqLit7 s {1, 4, 5, 6} h3 (by decide)
  · exact .inr <| .inr <| .inr <| .inr <| .inr <| eqLit7 s {2, 4, 5, 6} h4 (by decide)

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
