import AlbertsonBerman.Cycles
import AlbertsonBerman.ForestBound
import AlbertsonBerman.Transfer
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation

/-!
# Proved solution

Jung's 31-vertex seed is a spherical triangulation whose largest induced
forest has 15 vertices. Planarity certificates are finite `decide` checks
plus a BFS connectedness argument. The upper bound `a(G) ≤ 15` is Jung's
selected-edge transfer law on the two icosahedral gadgets, using the
explicit cycle/triangle profile of `X` and the pentagonal bipyramid.
-/

open Finset SimpleGraph AlbertsonBerman

namespace AlbertsonBerman

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

abbrev Vertex := Fin 31
abbrev Edge := Sym2 Vertex
abbrev Face := Vertex × Vertex × Vertex

def adjMask : Vertex → ℕ := ![
  4594, 12645, 18350186, 51380340, 105, 31, 1052703, 7937, 25219, 50560,
  100992, 201856, 141507, 413954, 303872, 345600, 429056, 342016, 253952,
  32505860, 103284812, 207093760, 413663232, 826802176, 579338252,
  1695547400, 1244659712, 1415577600, 1757413376, 1400897536, 1040187392]

def adjB (i j : Vertex) : Bool := (adjMask i).testBit j.val

lemma adjB_symm : ∀ x y, adjB x y = adjB y x := by decide
lemma adjB_irrefl : ∀ x, ¬ adjB x x := by decide

def G : SimpleGraph Vertex := SimpleGraph.mk' ⟨adjB, ⟨adjB_symm, adjB_irrefl⟩⟩

instance : DecidableRel G.Adj := fun i j => Bool.decEq (adjB i j) true

def seedEdges : Finset Edge :=
  ((univ ×ˢ univ).filter (fun p : Vertex × Vertex =>
      decide (p.1 < p.2) && adjB p.1 p.2)).image fun p => s(p.1, p.2)

def faces : Finset Face :=
  {(0, 1, 5), (0, 1, 8), (0, 4, 5), (0, 4, 6), (0, 6, 12), (0, 7, 8),
   (0, 7, 12), (1, 2, 5), (1, 2, 6), (1, 6, 12), (1, 8, 13), (1, 12, 13),
   (2, 3, 5), (2, 3, 24), (2, 6, 20), (2, 19, 20), (2, 19, 24), (3, 4, 5),
   (3, 4, 6), (3, 6, 20), (3, 20, 25), (3, 24, 25), (7, 8, 9), (7, 9, 10),
   (7, 10, 11), (7, 11, 12), (8, 9, 14), (8, 13, 14), (9, 10, 15), (9, 14, 15),
   (10, 11, 16), (10, 15, 16), (11, 12, 17), (11, 16, 17), (12, 13, 17),
   (13, 14, 18), (13, 17, 18), (14, 15, 18), (15, 16, 18), (16, 17, 18),
   (19, 20, 21), (19, 21, 22), (19, 22, 23), (19, 23, 24), (20, 21, 26),
   (20, 25, 26), (21, 22, 27), (21, 26, 27), (22, 23, 28), (22, 27, 28),
   (23, 24, 29), (23, 28, 29), (24, 25, 29), (25, 26, 30), (25, 29, 30),
   (26, 27, 30), (27, 28, 30), (28, 29, 30)}

def faceBoundary (t : Face) : Finset Edge :=
  {s(t.1, t.2.1), s(t.2.1, t.2.2), s(t.2.2, t.1)}

def witness : Finset Vertex :=
  {1, 3, 5, 7, 9, 11, 13, 14, 16, 20, 22, 23, 26, 27, 29}

/-- BFS tree of `G` rooted at vertex 0. -/
def bfsParent : Vertex → Vertex := ![
  0, 0, 1, 4, 0, 0, 0, 0, 0, 7, 7, 7, 0, 1, 8, 9, 10, 12, 13, 2, 6, 20, 19, 19, 2,
  3, 20, 21, 22, 24, 25]

def bfsHeight : Vertex → ℕ := ![
  0, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 3, 3, 2, 3, 4, 4, 3, 3, 3,
  4, 5, 4, 4]

lemma parent_adj (v : Vertex) (h : v ≠ 0) : adjB v (bfsParent v) = true := by
  fin_cases v <;> first | exact (h rfl).elim | decide

lemma height_succ (v : Vertex) (h : v ≠ 0) :
    bfsHeight (bfsParent v) + 1 = bfsHeight v := by
  fin_cases v <;> first | exact (h rfl).elim | decide

lemma reachable_from_zero : ∀ v : Vertex, G.Reachable 0 v := by
  intro v
  have : ∀ n v, bfsHeight v = n → G.Reachable 0 v := by
    intro n
    induction n with
    | zero =>
        intro v hv
        have : v = 0 := by
          fin_cases v <;> simp [bfsHeight] at hv ⊢
        subst v
        exact Reachable.refl _
    | succ n ih =>
        intro v hv
        have hv0 : v ≠ 0 := by
          rintro rfl
          simp [bfsHeight] at hv
        have hht : bfsHeight (bfsParent v) = n := by
          have := height_succ v hv0
          omega
        have : G.Adj v (bfsParent v) := parent_adj v hv0
        exact (ih (bfsParent v) hht).trans (Adj.reachable this.symm)
  exact this (bfsHeight v) v rfl

lemma G_connected : G.Connected :=
  (connected_iff_exists_forall_reachable (G := G)).2 ⟨0, reachable_from_zero⟩

lemma adj_pair_card :
    #((univ ×ˢ univ : Finset (Vertex × Vertex)).filter
        (fun p => decide (p.1 < p.2) && adjB p.1 p.2)) = 87 := by
  decide

lemma G_adj_iff {i j : Vertex} : G.Adj i j ↔ adjB i j = true := Iff.rfl

lemma mem_seedEdges {u v : Vertex} :
    s(u, v) ∈ seedEdges ↔ u ≠ v ∧ adjB u v = true := by
  simp only [seedEdges, mem_image, mem_filter, mem_product, mem_univ, true_and,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, hadj⟩, hsy⟩
    rcases p with ⟨i, j⟩
    rcases (Sym2.eq_iff.mp hsy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp.ne, hadj⟩
    · exact ⟨hp.ne.symm, (adjB_symm _ _) ▸ hadj⟩
  · intro ⟨hne, hadj⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨⟨u, v⟩, ⟨h, hadj⟩, rfl⟩
    · refine ⟨⟨v, u⟩, ⟨h, (adjB_symm u v) ▸ hadj⟩, Sym2.eq_swap⟩

lemma mem_seedEdges_exists {e : Edge} :
    e ∈ seedEdges ↔ ∃ i j : Vertex, i < j ∧ adjB i j = true ∧ e = s(i, j) := by
  refine Sym2.inductionOn e ?_
  intro u v
  rw [mem_seedEdges]
  constructor
  · intro ⟨hne, hadj⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨u, v, h, hadj, rfl⟩
    · exact ⟨v, u, h, (adjB_symm u v) ▸ hadj, Sym2.eq_swap⟩
  · rintro ⟨i, j, hij, hadj, he⟩
    rcases (Sym2.eq_iff.mp he) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hij.ne, hadj⟩
    · exact ⟨hij.ne.symm, (adjB_symm _ _) ▸ hadj⟩

lemma adj_ordered_card :
    #((univ : Finset (Vertex × Vertex)).filter fun p => adjB p.1 p.2) = 174 := by
  set P := (univ : Finset (Vertex × Vertex)).filter
    fun p => decide (p.1 < p.2) && adjB p.1 p.2
  set Q := (univ : Finset (Vertex × Vertex)).filter
    fun p => decide (p.2 < p.1) && adjB p.1 p.2
  have hP : #P = 87 := by
    simpa [P, Finset.univ_product_univ] using adj_pair_card
  have hswap : Q = P.image fun p => (p.2, p.1) := by
    ext p
    rcases p with ⟨i, j⟩
    simp only [Q, P, mem_image, mem_filter, mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · intro ⟨hji, hadj⟩
      exact ⟨⟨j, i⟩, ⟨hji, by rwa [adjB_symm]⟩, rfl, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨hab, hadj⟩, ha, hb⟩
      cases ha; cases hb
      exact ⟨hab, by rwa [adjB_symm]⟩
  have hQ : #Q = 87 := by
    rw [hswap, card_image_of_injective]
    · exact hP
    · intro p q hpq
      rcases p with ⟨a, b⟩
      rcases q with ⟨c, d⟩
      simp at hpq
      exact Prod.ext hpq.2 hpq.1
  have hsplit : (univ.filter fun p => adjB p.1 p.2) = P ∪ Q := by
    ext p
    rcases p with ⟨i, j⟩
    simp only [P, Q, mem_union, mem_filter, mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · intro hadj
      have hne : i ≠ j := fun h => adjB_irrefl i (h ▸ hadj)
      rcases lt_or_gt_of_ne hne with h | h
      · exact .inl ⟨h, hadj⟩
      · exact .inr ⟨h, hadj⟩
    · rintro (⟨_, hadj⟩ | ⟨_, hadj⟩) <;> exact hadj
  have disj : Disjoint P Q := by
    refine disjoint_left.2 ?_
    intro p hpP hpQ
    simp only [P, Q, mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hpP hpQ
    exact (lt_asymm hpP.2.1 hpQ.2.1).elim
  rw [hsplit, card_union_of_disjoint disj, hP, hQ]

lemma seedEdges_card : #seedEdges = 87 := by decide

lemma card_G_edgeFinset : #G.edgeFinset = 87 := by
  have h := two_mul_card_edgeFinset (G := G)
  have hfilter :
      (univ.filter fun p : Vertex × Vertex => G.Adj p.1 p.2) =
        univ.filter fun p => adjB p.1 p.2 := by
    ext p
    simp [G_adj_iff]
  rw [hfilter, adj_ordered_card] at h
  omega

lemma subset_seedEdges : G.edgeFinset ⊆ seedEdges := by
  intro e he
  induction e using Sym2.inductionOn
  rename_i u v
  rw [mem_edgeFinset, mem_edgeSet, G_adj_iff] at he
  exact mem_seedEdges.2 ⟨(G_adj_iff.2 he).ne, he⟩

lemma eq_seedEdges : G.edgeFinset = seedEdges :=
  eq_of_subset_of_card_le subset_seedEdges (by rw [card_G_edgeFinset, seedEdges_card])

lemma mem_faces_iff {t : Face} : t ∈ faces ↔
    t = (0, 1, 5) ∨
    t = (0, 1, 8) ∨
    t = (0, 4, 5) ∨
    t = (0, 4, 6) ∨
    t = (0, 6, 12) ∨
    t = (0, 7, 8) ∨
    t = (0, 7, 12) ∨
    t = (1, 2, 5) ∨
    t = (1, 2, 6) ∨
    t = (1, 6, 12) ∨
    t = (1, 8, 13) ∨
    t = (1, 12, 13) ∨
    t = (2, 3, 5) ∨
    t = (2, 3, 24) ∨
    t = (2, 6, 20) ∨
    t = (2, 19, 20) ∨
    t = (2, 19, 24) ∨
    t = (3, 4, 5) ∨
    t = (3, 4, 6) ∨
    t = (3, 6, 20) ∨
    t = (3, 20, 25) ∨
    t = (3, 24, 25) ∨
    t = (7, 8, 9) ∨
    t = (7, 9, 10) ∨
    t = (7, 10, 11) ∨
    t = (7, 11, 12) ∨
    t = (8, 9, 14) ∨
    t = (8, 13, 14) ∨
    t = (9, 10, 15) ∨
    t = (9, 14, 15) ∨
    t = (10, 11, 16) ∨
    t = (10, 15, 16) ∨
    t = (11, 12, 17) ∨
    t = (11, 16, 17) ∨
    t = (12, 13, 17) ∨
    t = (13, 14, 18) ∨
    t = (13, 17, 18) ∨
    t = (14, 15, 18) ∨
    t = (15, 16, 18) ∨
    t = (16, 17, 18) ∨
    t = (19, 20, 21) ∨
    t = (19, 21, 22) ∨
    t = (19, 22, 23) ∨
    t = (19, 23, 24) ∨
    t = (20, 21, 26) ∨
    t = (20, 25, 26) ∨
    t = (21, 22, 27) ∨
    t = (21, 26, 27) ∨
    t = (22, 23, 28) ∨
    t = (22, 27, 28) ∨
    t = (23, 24, 29) ∨
    t = (23, 28, 29) ∨
    t = (24, 25, 29) ∨
    t = (25, 26, 30) ∨
    t = (25, 29, 30) ∨
    t = (26, 27, 30) ∨
    t = (27, 28, 30) ∨
    t = (28, 29, 30) := by
  simp [faces]

lemma faces_sorted_adj :
    ∀ t ∈ faces, t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
      adjB t.1 t.2.1 = true ∧ adjB t.2.1 t.2.2 = true ∧ adjB t.2.2 t.1 = true := by
  intro t ht
  rcases (mem_faces_iff.mp ht) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

lemma tris_lemma : ∀ t ∈ faces, t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1 := by
  intro t ht
  have h := faces_sorted_adj t ht
  exact ⟨h.1, h.2.1, G_adj_iff.2 h.2.2.1, G_adj_iff.2 h.2.2.2.1, G_adj_iff.2 h.2.2.2.2⟩

/-- Whether the ordered pair `(i,j)` is one of the three increasing pairs of a face. -/
def faceHits (i j : Vertex) (t : Face) : Bool :=
  (i == t.1 && j == t.2.1) || (i == t.2.1 && j == t.2.2) || (i == t.1 && j == t.2.2)

lemma faceHits_iff {i j : Vertex} {t : Face} (hij : i < j)
    (hs : t.1 < t.2.1 ∧ t.2.1 < t.2.2) :
    s(i, j) ∈ faceBoundary t ↔ faceHits i j t = true := by
  have h13 : t.1 < t.2.2 := lt_trans hs.1 hs.2
  simp only [faceBoundary, faceHits, mem_insert, mem_singleton, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    rcases h with h | h | h
    · rcases (Sym2.eq_iff.mp h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl (.inl ⟨rfl, rfl⟩)
      · exact (lt_asymm hij hs.1).elim
    · rcases (Sym2.eq_iff.mp h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl (.inr ⟨rfl, rfl⟩)
      · exact (lt_asymm hij hs.2).elim
    · rcases (Sym2.eq_iff.mp h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (lt_asymm hij h13).elim
      · exact .inr ⟨rfl, rfl⟩
  · intro h
    rcases h with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩
    · simp
    · simp
    · simp [Sym2.eq_swap]

lemma inc_pairs :
    ∀ i j : Vertex, i < j → adjB i j = true → #{t ∈ faces | faceHits i j t} = 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

lemma inc_lemma : ∀ e ∈ seedEdges, #{t ∈ faces | e ∈ faceBoundary t} = 2 := by
  intro e he
  obtain ⟨i, j, hij, hadj, rfl⟩ := mem_seedEdges_exists.mp he
  have hset :
      {t ∈ faces | s(i, j) ∈ faceBoundary t} = {t ∈ faces | faceHits i j t} := by
    ext t
    simp only [mem_filter, and_congr_right_iff]
    intro ht
    have hs := faces_sorted_adj t ht
    simpa using (faceHits_iff hij ⟨hs.1, hs.2.1⟩)
  rw [hset]
  exact inc_pairs i j hij hadj

lemma cover_lemma : ∀ t ∈ faces, faceBoundary t ⊆ seedEdges := by
  intro t ht e he
  have hs := faces_sorted_adj t ht
  have htri := tris_lemma t ht
  simp only [faceBoundary, mem_insert, mem_singleton] at he
  rcases he with he | he | he
  · subst e
    exact mem_seedEdges.2 ⟨htri.1.ne, hs.2.2.1⟩
  · subst e
    exact mem_seedEdges.2 ⟨htri.2.1.ne, hs.2.2.2.1⟩
  · subst e
    exact mem_seedEdges.2 ⟨htri.2.2.2.2.ne, hs.2.2.2.2⟩

lemma euler_lemma : Fintype.card Vertex + #faces = #seedEdges + 2 := by
  have hV : Fintype.card Vertex = 31 := by decide
  have hf : #faces = 58 := by decide
  have he := seedEdges_card
  omega

/-- BFS tree of the 15-vertex witness, rooted at 5. -/
def wParent (v : Vertex) : Vertex :=
  match v.val with
  | 1 => 5 | 3 => 5 | 5 => 5 | 13 => 1 | 14 => 13 | 9 => 14 | 7 => 9 | 11 => 7
  | 16 => 11 | 20 => 3 | 26 => 20 | 27 => 26 | 22 => 27 | 23 => 22 | 29 => 23
  | _ => v

def wHeight (v : Vertex) : ℕ :=
  match v.val with
  | 5 => 0 | 1 | 3 => 1 | 13 | 20 => 2 | 14 | 26 => 3 | 9 | 27 => 4
  | 7 | 22 => 5 | 11 | 23 => 6 | 16 | 29 => 7 | _ => 0

lemma wParent_mem {v : Vertex} (hv : v ∈ witness) : wParent v ∈ witness := by
  fin_cases v <;> simp [wParent, witness] at hv ⊢

lemma wParent_adj {v : Vertex} (hv : v ∈ witness) (h : v ≠ 5) :
    adjB v (wParent v) = true := by
  fin_cases v <;> simp [wParent, witness] at hv h ⊢ <;>
    first | exact (h rfl).elim | exact False.elim hv | decide

lemma wHeight_succ {v : Vertex} (hv : v ∈ witness) (h : v ≠ 5) :
    wHeight (wParent v) + 1 = wHeight v := by
  fin_cases v <;> simp [wParent, wHeight, witness] at hv h ⊢ <;>
    first | exact (h rfl).elim | exact False.elim hv | decide

lemma witness_reachable_root (v : Vertex) (hv : v ∈ witness) :
    (G.induce (witness : Set Vertex)).Reachable ⟨5, by decide⟩ ⟨v, hv⟩ := by
  have : ∀ n v (hv : v ∈ witness), wHeight v = n →
      (G.induce (witness : Set Vertex)).Reachable ⟨5, by decide⟩ ⟨v, hv⟩ := by
    intro n
    induction n with
    | zero =>
        intro v hv ht
        have : v = 5 := by
          fin_cases v <;> simp [wHeight, witness] at hv ht ⊢
        subst v
        exact Reachable.refl _
    | succ n ih =>
        intro v hv ht
        have hv5 : v ≠ 5 := by
          rintro rfl
          simp [wHeight] at ht
        have hht : wHeight (wParent v) = n := by
          have := wHeight_succ hv hv5
          omega
        have hadj :
            (G.induce (witness : Set Vertex)).Adj ⟨v, hv⟩ ⟨wParent v, wParent_mem hv⟩ :=
          wParent_adj hv hv5
        exact (ih (wParent v) (wParent_mem hv) hht).trans hadj.reachable.symm
  exact this (wHeight v) v hv rfl

lemma witness_connected : (G.induce (witness : Set Vertex)).Connected :=
  (connected_iff_exists_forall_reachable (G := G.induce (witness : Set Vertex))).2
    ⟨⟨5, by decide⟩, fun y => witness_reachable_root y.1 y.2⟩

lemma witness_ordered_adj :
    #((univ : Finset ({x // x ∈ witness} × {y // y ∈ witness})).filter
        fun p => adjB p.1.1 p.2.1) = 28 := by
  decide

/-- The 15-vertex witness induces a tree, hence is acyclic. -/
lemma witness_acyclic : (G.induce (witness : Set Vertex)).IsAcyclic := by
  have htree : (G.induce (witness : Set Vertex)).IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨witness_connected, ?_⟩
    simp only [Nat.card_eq_fintype_card, ← edgeFinset_card]
    have hW : Fintype.card {v // v ∈ witness} = 15 := by
      rw [Fintype.card_coe]
      decide
    have h2 := two_mul_card_edgeFinset (G := G.induce (witness : Set Vertex))
    let W := {v : Vertex // v ∈ witness}
    have hfilter :
        (univ.filter fun p : W × W => (G.induce (witness : Set Vertex)).Adj p.1 p.2) =
          univ.filter fun p : W × W => adjB p.1.1 p.2.1 := by
      ext p
      simp [G_adj_iff]
    change 2 * #(G.induce (witness : Set Vertex)).edgeFinset =
      #(univ.filter fun p : W × W => (G.induce (witness : Set Vertex)).Adj p.1 p.2) at h2
    rw [hfilter] at h2
    have hord : #(univ.filter fun p : W × W => adjB p.1.1 p.2.1) = 28 :=
      witness_ordered_adj
    rw [hord] at h2
    have hE : #(G.induce (witness : Set Vertex)).edgeFinset = 14 := by omega
    rw [hE]
    have : Fintype.card {v // v ∈ (witness : Set Vertex)} = 15 := by
      rw [Fintype.card_subtype]
      change #({x : Vertex | x ∈ witness}.toFinset) = 15
      simp
      decide
    exact this
  exact htree.isAcyclic

def baseVerts : Finset Vertex := {0, 1, 2, 3, 4, 5, 6}
def internals1 : Finset Vertex := {7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18}
def internals2 : Finset Vertex := {19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}

lemma parts_cover : baseVerts ∪ internals1 ∪ internals2 = univ := by decide
lemma disjoint_base_int1 : Disjoint baseVerts internals1 := by decide
lemma disjoint_base_int2 : Disjoint baseVerts internals2 := by decide
lemma disjoint_int1_int2 : Disjoint internals1 internals2 := by decide

lemma card_parts (s : Finset Vertex) :
    #s = #(s ∩ baseVerts) + #(s ∩ internals1) + #(s ∩ internals2) := by
  have hunion :
      s ∩ (baseVerts ∪ internals1 ∪ internals2) =
        s ∩ baseVerts ∪ s ∩ internals1 ∪ s ∩ internals2 := by
    simp [inter_union_distrib_left]
  have hs : s ∩ univ = s := inter_univ s
  have d1 : Disjoint (s ∩ baseVerts) (s ∩ internals1) :=
    disjoint_base_int1.mono inter_subset_right inter_subset_right
  have d2 : Disjoint (s ∩ baseVerts ∪ s ∩ internals1) (s ∩ internals2) := by
    refine disjoint_union_left.2 ⟨?_, ?_⟩
    · exact disjoint_base_int2.mono inter_subset_right inter_subset_right
    · exact disjoint_int1_int2.mono inter_subset_right inter_subset_right
  calc
    #s = #(s ∩ univ) := by rw [hs]
    _ = #(s ∩ (baseVerts ∪ internals1 ∪ internals2)) := by rw [parts_cover]
    _ = #(s ∩ baseVerts ∪ s ∩ internals1 ∪ s ∩ internals2) := by rw [hunion]
    _ = #(s ∩ baseVerts ∪ s ∩ internals1) + #(s ∩ internals2) :=
      card_union_of_disjoint d2
    _ = #(s ∩ baseVerts) + #(s ∩ internals1) + #(s ∩ internals2) := by
      rw [card_union_of_disjoint d1]

/-- Local vertices of the first gadget copy, terminals at indices 6 and 7. -/
def gadget1 : Fin 14 → Vertex := ![7, 8, 9, 10, 11, 12, 0, 1, 13, 14, 15, 16, 17, 18]

/-- Local vertices of the second gadget copy, terminals at indices 6 and 7. -/
def gadget2 : Fin 14 → Vertex := ![19, 20, 21, 22, 23, 24, 2, 3, 25, 26, 27, 28, 29, 30]

def baseCast (i : Fin 7) : Vertex := i.castLE (by decide : 7 ≤ 31)

lemma gadget1_inj : Function.Injective gadget1 := by decide
lemma gadget2_inj : Function.Injective gadget2 := by decide
lemma baseCast_inj : Function.Injective baseCast := by decide

lemma gadget1_xAdjB (i j : Fin 14) : adjB (gadget1 i) (gadget1 j) = xAdjB i j := by
  fin_cases i <;> fin_cases j <;> decide

lemma gadget2_xAdjB (i j : Fin 14) : adjB (gadget2 i) (gadget2 j) = xAdjB i j := by
  fin_cases i <;> fin_cases j <;> decide

lemma baseCast_bAdjB (i j : Fin 7) : adjB (baseCast i) (baseCast j) = bAdjB i j := by
  fin_cases i <;> fin_cases j <;> decide

lemma gadget1_adj_iff {i j : Fin 14} :
    G.Adj (gadget1 i) (gadget1 j) ↔ X.Adj i j := by
  rw [G_adj_iff, xAdjB_iff, gadget1_xAdjB]

lemma gadget2_adj_iff {i j : Fin 14} :
    G.Adj (gadget2 i) (gadget2 j) ↔ X.Adj i j := by
  rw [G_adj_iff, xAdjB_iff, gadget2_xAdjB]

lemma baseCast_adj_iff {i j : Fin 7} :
    G.Adj (baseCast i) (baseCast j) ↔ B.Adj i j := by
  rw [G_adj_iff, bAdjB_iff, baseCast_bAdjB]

def gadget1Emb : X ↪g G where
  toFun := gadget1
  inj' := gadget1_inj
  map_rel_iff' := gadget1_adj_iff

def gadget2Emb : X ↪g G where
  toFun := gadget2
  inj' := gadget2_inj
  map_rel_iff' := gadget2_adj_iff

def baseEmb : B ↪g G where
  toFun := baseCast
  inj' := baseCast_inj
  map_rel_iff' := baseCast_adj_iff

def pre1 (y : Finset Vertex) : Finset (Fin 14) :=
  univ.filter fun i => gadget1 i ∈ y

def pre2 (y : Finset Vertex) : Finset (Fin 14) :=
  univ.filter fun i => gadget2 i ∈ y

def preB (S : Finset Vertex) : Finset (Fin 7) :=
  univ.filter fun i => baseCast i ∈ S

lemma gadget1_covers_internals1 :
    internals1 ⊆ (univ : Finset (Fin 14)).image gadget1 := by decide
lemma gadget2_covers_internals2 :
    internals2 ⊆ (univ : Finset (Fin 14)).image gadget2 := by decide
lemma baseCast_covers : baseVerts ⊆ (univ : Finset (Fin 7)).image baseCast := by decide

lemma gadget1_mem_internals1 {i : Fin 14} :
    gadget1 i ∈ internals1 ↔ i ≠ 6 ∧ i ≠ 7 := by
  fin_cases i <;> decide

lemma gadget2_mem_internals2 {i : Fin 14} :
    gadget2 i ∈ internals2 ↔ i ≠ 6 ∧ i ≠ 7 := by
  fin_cases i <;> decide

lemma baseCast_mem_base {i : Fin 7} : baseCast i ∈ baseVerts := by
  fin_cases i <;> decide

lemma pre1_card {y : Finset Vertex} (hy : y ⊆ internals1) : #(pre1 y) = #y := by
  refine card_nbij gadget1 ?_ ?_ ?_
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro i j _ _ h
    exact gadget1_inj h
  · intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp (gadget1_covers_internals1 (hy hv))
    exact ⟨i, mem_filter.2 ⟨mem_univ i, by simpa using hv⟩, rfl⟩

lemma pre1_not_term {y : Finset Vertex} (hy : y ⊆ internals1) {i : Fin 14}
    (hi : i ∈ pre1 y) : i ≠ 6 ∧ i ≠ 7 := by
  simp only [pre1, mem_filter] at hi
  exact gadget1_mem_internals1.mp (hy hi.2)

lemma pre1_image {y : Finset Vertex} (hy : y ⊆ internals1) :
    (pre1 y).image gadget1 = y := by
  ext v
  simp only [mem_image, pre1, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp (gadget1_covers_internals1 (hy hv))
    exact ⟨i, hv, rfl⟩

lemma pre2_card {y : Finset Vertex} (hy : y ⊆ internals2) : #(pre2 y) = #y := by
  refine card_nbij gadget2 ?_ ?_ ?_
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro i j _ _ h
    exact gadget2_inj h
  · intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp (gadget2_covers_internals2 (hy hv))
    exact ⟨i, mem_filter.2 ⟨mem_univ i, by simpa using hv⟩, rfl⟩

lemma pre2_not_term {y : Finset Vertex} (hy : y ⊆ internals2) {i : Fin 14}
    (hi : i ∈ pre2 y) : i ≠ 6 ∧ i ≠ 7 := by
  simp only [pre2, mem_filter] at hi
  exact gadget2_mem_internals2.mp (hy hi.2)

lemma pre2_image {y : Finset Vertex} (hy : y ⊆ internals2) :
    (pre2 y).image gadget2 = y := by
  ext v
  simp only [mem_image, pre2, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp (gadget2_covers_internals2 (hy hv))
    exact ⟨i, hv, rfl⟩

lemma preB_card {S : Finset Vertex} (hS : S ⊆ baseVerts) : #(preB S) = #S := by
  refine card_nbij baseCast ?_ ?_ ?_
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro i j _ _ h
    exact baseCast_inj h
  · intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp (baseCast_covers (hS hv))
    exact ⟨i, mem_filter.2 ⟨mem_univ i, by simpa using hv⟩, rfl⟩

lemma preB_image {S : Finset Vertex} (hS : S ⊆ baseVerts) :
    (preB S).image baseCast = S := by
  ext v
  simp only [mem_image, preB, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp (baseCast_covers (hS hv))
    exact ⟨i, hv, rfl⟩

lemma preB_mem0 {S : Finset Vertex} : 0 ∈ preB S ↔ 0 ∈ S := by
  simp [preB, baseCast]
lemma preB_mem1 {S : Finset Vertex} : 1 ∈ preB S ↔ 1 ∈ S := by
  simp [preB, baseCast]
lemma preB_mem2 {S : Finset Vertex} : 2 ∈ preB S ↔ 2 ∈ S := by
  simp [preB, baseCast]
lemma preB_mem3 {S : Finset Vertex} : 3 ∈ preB S ↔ 3 ∈ S := by
  simp [preB, baseCast]

lemma seven_int1_not_acyclic (y : Finset Vertex) (hy : y ⊆ internals1) (hc : #y = 7) :
    ¬ (G.induce (y : Set Vertex)).IsAcyclic := by
  have h6 : 6 ∉ pre1 y := fun h => (pre1_not_term hy h).1 rfl
  have h7 : 7 ∉ pre1 y := fun h => (pre1_not_term hy h).2 rfl
  have hcard : #(pre1 y) = 7 := by rw [pre1_card hy, hc]
  have hx : ¬ (X.induce (pre1 y : Set (Fin 14))).IsAcyclic :=
    seven_int_not_acyclic _ h6 h7 hcard
  have himg : (gadget1Emb : _ → _) '' (pre1 y : Set (Fin 14)) ⊆ (y : Set Vertex) := by
    intro v ⟨i, hi, hv⟩
    subst hv
    have : gadget1 i ∈ y := (mem_filter.mp hi).2
    simpa [gadget1Emb] using this
  exact not_acyclic_of_embedding_image gadget1Emb himg hx

lemma seven_int2_not_acyclic (y : Finset Vertex) (hy : y ⊆ internals2) (hc : #y = 7) :
    ¬ (G.induce (y : Set Vertex)).IsAcyclic := by
  have h6 : 6 ∉ pre2 y := fun h => (pre2_not_term hy h).1 rfl
  have h7 : 7 ∉ pre2 y := fun h => (pre2_not_term hy h).2 rfl
  have hcard : #(pre2 y) = 7 := by rw [pre2_card hy, hc]
  have hx : ¬ (X.induce (pre2 y : Set (Fin 14))).IsAcyclic :=
    seven_int_not_acyclic _ h6 h7 hcard
  have himg : (gadget2Emb : _ → _) '' (pre2 y : Set (Fin 14)) ⊆ (y : Set Vertex) := by
    intro v ⟨i, hi, hv⟩
    subst hv
    have : gadget2 i ∈ y := (mem_filter.mp hi).2
    simpa [gadget2Emb] using this
  exact not_acyclic_of_embedding_image gadget2Emb himg hx

lemma six_int1_terminals_not_acyclic (y : Finset Vertex)
    (hy : y ⊆ internals1) (hc : #y = 6) :
    ¬ (G.induce ((y : Set Vertex) ∪ {0, 1})).IsAcyclic := by
  let s : Finset (Fin 14) := pre1 y ∪ {6, 7}
  have h6 : 6 ∈ s := by simp [s]
  have h7 : 7 ∈ s := by simp [s]
  have hdis : Disjoint (pre1 y) ({6, 7} : Finset (Fin 14)) := by
    refine disjoint_left.2 ?_
    intro i hi hterm
    have nt := pre1_not_term hy hi
    simp only [mem_insert, mem_singleton] at hterm
    rcases hterm with rfl | rfl
    · exact nt.1 rfl
    · exact nt.2 rfl
  have hcard : #s = 8 := by
    change #(pre1 y ∪ {6, 7}) = 8
    rw [card_union_of_disjoint hdis, pre1_card hy, hc]
    decide
  have hx : ¬ (X.induce (s : Set (Fin 14))).IsAcyclic :=
    gh_eight_not_acyclic s h6 h7 hcard
  have himg :
      (gadget1Emb : _ → _) '' (s : Set (Fin 14)) ⊆ ((y : Set Vertex) ∪ {0, 1}) := by
    intro v ⟨i, hi, hv⟩
    subst hv
    have hi' : i = 6 ∨ i = 7 ∨ i ∈ pre1 y := by
      simpa [s] using hi
    rcases hi' with rfl | rfl | hi'
    · simp [gadget1Emb, gadget1]
    · simp [gadget1Emb, gadget1]
    · left
      exact (mem_filter.mp hi').2
  exact not_acyclic_of_embedding_image gadget1Emb himg hx

lemma six_int2_terminals_not_acyclic (y : Finset Vertex)
    (hy : y ⊆ internals2) (hc : #y = 6) :
    ¬ (G.induce ((y : Set Vertex) ∪ {2, 3})).IsAcyclic := by
  let s : Finset (Fin 14) := pre2 y ∪ {6, 7}
  have h6 : 6 ∈ s := by simp [s]
  have h7 : 7 ∈ s := by simp [s]
  have hdis : Disjoint (pre2 y) ({6, 7} : Finset (Fin 14)) := by
    refine disjoint_left.2 ?_
    intro i hi hterm
    have nt := pre2_not_term hy hi
    simp only [mem_insert, mem_singleton] at hterm
    rcases hterm with rfl | rfl
    · exact nt.1 rfl
    · exact nt.2 rfl
  have hcard : #s = 8 := by
    change #(pre2 y ∪ {6, 7}) = 8
    rw [card_union_of_disjoint hdis, pre2_card hy, hc]
    decide
  have hx : ¬ (X.induce (s : Set (Fin 14))).IsAcyclic :=
    gh_eight_not_acyclic s h6 h7 hcard
  have himg :
      (gadget2Emb : _ → _) '' (s : Set (Fin 14)) ⊆ ((y : Set Vertex) ∪ {2, 3}) := by
    intro v ⟨i, hi, hv⟩
    subst hv
    have hi' : i = 6 ∨ i = 7 ∨ i ∈ pre2 y := by
      simpa [s] using hi
    rcases hi' with rfl | rfl | hi'
    · simp [gadget2Emb, gadget2]
    · simp [gadget2Emb, gadget2]
    · left
      exact (mem_filter.mp hi').2
  exact not_acyclic_of_embedding_image gadget2Emb himg hx

lemma phi_preB (S : Finset Vertex) :
    phi (preB S) =
      #(preB S) - (if 0 ∈ S ∧ 1 ∈ S then 1 else 0) - (if 2 ∈ S ∧ 3 ∈ S then 1 else 0) := by
  simp [phi, preB_mem0, preB_mem1, preB_mem2, preB_mem3]

lemma base_phi_not_acyclic (S : Finset Vertex) (hS : S ⊆ baseVerts)
    (hφ : 4 ≤ #S - (if 0 ∈ S ∧ 1 ∈ S then 1 else 0) - (if 2 ∈ S ∧ 3 ∈ S then 1 else 0)) :
    ¬ (G.induce (S : Set Vertex)).IsAcyclic := by
  have hφ' : 4 ≤ phi (preB S) := by
    rw [phi_preB, preB_card hS]
    exact hφ
  have hx : ¬ (B.induce (preB S : Set (Fin 7))).IsAcyclic :=
    b_phi_not_acyclic _ hφ'
  have himg : (baseEmb : _ → _) '' (preB S : Set (Fin 7)) ⊆ (S : Set Vertex) := by
    intro v ⟨i, hi, hv⟩
    subst hv
    have : baseCast i ∈ S := (mem_filter.mp hi).2
    simpa [baseEmb] using this
  exact not_acyclic_of_embedding_image baseEmb himg hx

lemma no_sixteen (s : Finset Vertex) (hs : #s = 16) :
    ¬ (G.induce (s : Set Vertex)).IsAcyclic := by
  intro hac
  let S := s ∩ baseVerts
  let Y1 := s ∩ internals1
  let Y2 := s ∩ internals2
  have hsum : #s = #S + #Y1 + #Y2 := card_parts s
  have y1le6 : #Y1 ≤ 6 := by
    by_contra h
    obtain ⟨t, ht, htc⟩ := exists_subset_card_eq (s := Y1) (n := 7) (by omega)
    have htI : t ⊆ internals1 := ht.trans inter_subset_right
    have htS : (t : Set Vertex) ⊆ s := by
      intro x hx
      exact inter_subset_left (ht hx)
    exact seven_int1_not_acyclic t htI htc (induce_subset_acyclic htS hac)
  have y2le6 : #Y2 ≤ 6 := by
    by_contra h
    obtain ⟨t, ht, htc⟩ := exists_subset_card_eq (s := Y2) (n := 7) (by omega)
    have htI : t ⊆ internals2 := ht.trans inter_subset_right
    have htS : (t : Set Vertex) ⊆ s := by
      intro x hx
      exact inter_subset_left (ht hx)
    exact seven_int2_not_acyclic t htI htc (induce_subset_acyclic htS hac)
  have y1e : #Y1 + (if 0 ∈ S ∧ 1 ∈ S then 1 else 0) ≤ 6 := by
    by_cases h01 : 0 ∈ S ∧ 1 ∈ S
    · simp only [h01]
      by_cases h6 : #Y1 = 6
      · have h0 : (0 : Vertex) ∈ s := inter_subset_left h01.1
        have h1 : (1 : Vertex) ∈ s := inter_subset_left h01.2
        have hsub : ((Y1 : Set Vertex) ∪ {0, 1}) ⊆ s := by
          intro x hx
          rcases hx with hx | hx
          · exact inter_subset_left hx
          · simp at hx
            rcases hx with rfl | rfl <;> assumption
        exact (six_int1_terminals_not_acyclic Y1 inter_subset_right h6
          (induce_subset_acyclic hsub hac)).elim
      · have hle : #Y1 ≤ 5 := Nat.lt_succ_iff.mp (lt_of_le_of_ne y1le6 h6)
        exact Nat.succ_le_succ hle
    · simp only [h01, ite_false]
      exact y1le6
  have y2e : #Y2 + (if 2 ∈ S ∧ 3 ∈ S then 1 else 0) ≤ 6 := by
    by_cases h23 : 2 ∈ S ∧ 3 ∈ S
    · simp only [h23]
      by_cases h6 : #Y2 = 6
      · have h2 : (2 : Vertex) ∈ s := inter_subset_left h23.1
        have h3 : (3 : Vertex) ∈ s := inter_subset_left h23.2
        have hsub : ((Y2 : Set Vertex) ∪ {2, 3}) ⊆ s := by
          intro x hx
          rcases hx with hx | hx
          · exact inter_subset_left hx
          · simp at hx
            rcases hx with rfl | rfl <;> assumption
        exact (six_int2_terminals_not_acyclic Y2 inter_subset_right h6
          (induce_subset_acyclic hsub hac)).elim
      · have hle : #Y2 ≤ 5 := Nat.lt_succ_iff.mp (lt_of_le_of_ne y2le6 h6)
        exact Nat.succ_le_succ hle
    · simp only [h23, ite_false]
      exact y2le6
  have hφ :
      4 ≤ #S - (if 0 ∈ S ∧ 1 ∈ S then 1 else 0) - (if 2 ∈ S ∧ 3 ∈ S then 1 else 0) := by
    have he01 : (if 0 ∈ S ∧ 1 ∈ S then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have he23 : (if 2 ∈ S ∧ 3 ∈ S then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have : (if 0 ∈ S ∧ 1 ∈ S then 1 else 0) + (if 2 ∈ S ∧ 3 ∈ S then 1 else 0) ≤ #S := by
      omega
    omega
  have hS : S ⊆ baseVerts := inter_subset_right
  have hsub : (S : Set Vertex) ⊆ s := inter_subset_left
  exact base_phi_not_acyclic S hS hφ (induce_subset_acyclic hsub hac)

theorem counterexample :
    #seedEdges = 87 ∧
    #G.edgeFinset = 87 ∧
    G.Connected ∧
    #faces = 58 ∧
    (∀ t ∈ faces, t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
      G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1) ∧
    (∀ e ∈ seedEdges, #{t ∈ faces | e ∈ faceBoundary t} = 2) ∧
    (∀ t ∈ faces, faceBoundary t ⊆ seedEdges) ∧
    G.edgeFinset = seedEdges ∧
    Fintype.card Vertex + #faces = #seedEdges + 2 ∧
    #witness = 15 ∧
    (G.induce (witness : Set Vertex)).IsAcyclic ∧
    ∀ s : Finset Vertex, #s = 16 → ¬ (G.induce (s : Set Vertex)).IsAcyclic := by
  exact ⟨by decide, card_G_edgeFinset, G_connected, by decide, tris_lemma, inc_lemma,
    cover_lemma, eq_seedEdges, euler_lemma, by decide, witness_acyclic, no_sixteen⟩

end AlbertsonBerman
