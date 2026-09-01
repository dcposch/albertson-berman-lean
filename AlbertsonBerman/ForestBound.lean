import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
Finite certificates that an induced subgraph is not a forest: a triangle, or
an explicit cycle whose support lies in the vertex set.
-/

open SimpleGraph

namespace AlbertsonBerman

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

instance {u v : V} (p : G.Walk u v) : Decidable p.IsTrail :=
  decidable_of_iff' _ (Walk.isTrail_def p)

instance {u : V} (p : G.Walk u u) : Decidable p.IsCycle :=
  decidable_of_iff' _ (Walk.isCycle_def p)

lemma not_isAcyclic_of_triangle {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ¬ G.IsAcyclic := by
  intro h
  have hc : G.IsNClique 3 {a, b, c} := by
    rw [is3Clique_triple_iff]
    exact ⟨hab, hca.symm, hbc⟩
  exact h.cliqueFree (by decide : (3 : ℕ) ≤ 3) _ hc

lemma not_isAcyclic_of_triangle_in
    {s : Finset V} {a b c : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    ¬ (G.induce (s : Set V)).IsAcyclic :=
  not_isAcyclic_of_triangle (G := G.induce (s : Set V))
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc⟩)
    (induce_adj.mpr hab) (induce_adj.mpr hbc) (induce_adj.mpr hca)

omit [DecidableEq V] in
lemma isCycle_induce {s : Set V} {u : V}
    (w : G.Walk u u) (hw : w.IsCycle) (hs : ∀ x ∈ w.support, x ∈ s) :
    (w.induce s hs).IsCycle := by
  have hinj : Function.Injective (Embedding.induce (s := s) (G := G)).toHom :=
    (Embedding.induce (s := s) (G := G)).injective
  have hmap : ((w.induce s hs).map (Embedding.induce s).toHom).IsCycle := by
    simpa [Walk.map_induce] using hw
  exact (Walk.isCycle_map_iff_of_injective hinj).1 hmap

omit [DecidableEq V] in
lemma not_isAcyclic_of_cycle {s : Set V} {u : V}
    (w : G.Walk u u) (hw : w.IsCycle) (hs : ∀ x ∈ w.support, x ∈ s) :
    ¬ (G.induce s).IsAcyclic :=
  fun h => h (w.induce s hs) (isCycle_induce w hw hs)

omit [DecidableEq V] in
lemma induce_subset_acyclic {s t : Set V}
    (h : t ⊆ s) (hac : (G.induce s).IsAcyclic) : (G.induce t).IsAcyclic :=
  hac.embedding (induceHomOfLE (G := G) h)

omit [DecidableEq V] in
/-- An injective adjacency-reflecting embedding pulls cycles back: if the image of
`s` sits in `t` and `G[s]` is not a forest, then `G'[t]` is not a forest. -/
lemma not_acyclic_of_embedding_image
    {W : Type*} [DecidableEq W] {G' : SimpleGraph W}
    (f : G ↪g G') {s : Set V} {t : Set W}
    (hst : (f : V → W) '' s ⊆ t) (h : ¬ (G.induce s).IsAcyclic) :
    ¬ (G'.induce t).IsAcyclic := by
  intro hac
  refine h ?_
  let e : G.induce s ↪g G'.induce ((f : V → W) '' s) :=
    { toFun := fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
      inj' := by
        intro a b hab
        exact Subtype.ext (f.injective (Subtype.ext_iff.mp hab))
      map_rel_iff' := by
        intro a b
        exact f.map_adj_iff }
  exact (induce_subset_acyclic hst hac).embedding e

end AlbertsonBerman
