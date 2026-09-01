import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation

/-!
# Albertson–Berman conjecture is false

Albertson and Berman (1979) conjectured that every planar graph on `n`
vertices contains an induced forest of order at least `n / 2`. This file
records Jung's explicit counterexample: the 31-vertex maximal planar graph
`G` obtained by substituting two copies of a 14-vertex icosahedral gadget
into a pentagonal bipyramid and adding the two completion edges `6--12`
and `6--20`.

Planarity is certified by a spherical triangulation: 58 triangular faces,
every edge in exactly two faces, Euler characteristic `31 - 87 + 58 = 2`.
The induced-forest number is exactly 15: the displayed 15-vertex set is an
induced tree, and no 16-vertex set is acyclic.

The compared theorem is the conjunction of these certificates. The gadget
profile, selected-edge transfer law, and the remaining proofs live in
`Solution.lean`. This statement does not claim that 29 is the minimum
order of a counterexample.
-/

open Finset SimpleGraph

namespace AlbertsonBerman

abbrev Vertex := Fin 31
abbrev Edge := Sym2 Vertex
abbrev Face := Vertex × Vertex × Vertex

/-- Neighbor bit-masks of the seed: vertex `i` is adjacent to `j` iff
`(adjMask i).testBit j`. -/
def adjMask : Vertex → ℕ := ![
  4594, 12645, 18350186, 51380340, 105, 31, 1052703, 7937, 25219, 50560,
  100992, 201856, 141507, 413954, 303872, 345600, 429056, 342016, 253952,
  32505860, 103284812, 207093760, 413663232, 826802176, 579338252,
  1695547400, 1244659712, 1415577600, 1757413376, 1400897536, 1040187392]

/-- Boolean adjacency of the seed. -/
def adjB (i j : Vertex) : Bool := (adjMask i).testBit j.val

lemma adjB_symm : ∀ x y, adjB x y = adjB y x := by decide
lemma adjB_irrefl : ∀ x, ¬ adjB x x := by decide

/-- Jung's 31-vertex seed. -/
def G : SimpleGraph Vertex := SimpleGraph.mk' ⟨adjB, ⟨adjB_symm, adjB_irrefl⟩⟩

instance : DecidableRel G.Adj := fun i j => Bool.decEq (adjB i j) true

/-- The 87 edges of the seed, as unordered pairs `i < j` with `adjB i j`. -/
def seedEdges : Finset Edge :=
  ((univ ×ˢ univ).filter (fun p : Vertex × Vertex =>
      decide (p.1 < p.2) && adjB p.1 p.2)).image fun p => s(p.1, p.2)

/-- Unoriented triangular faces of the seed, written with increasing labels. -/
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

/-- The three edges of an unoriented triangular face. -/
def faceBoundary (t : Face) : Finset Edge :=
  {s(t.1, t.2.1), s(t.2.1, t.2.2), s(t.2.2, t.1)}

/-- Jung's 15-vertex induced tree in the seed. -/
def witness : Finset Vertex :=
  {1, 3, 5, 7, 9, 11, 13, 14, 16, 20, 22, 23, 26, 27, 29}

/-- **Albertson–Berman (1979) is false.** The displayed 31-vertex simple graph
is a spherical triangulation (hence maximal planar) whose largest induced
forest has 15 vertices, so the induced-forest number need not be at least
`n / 2`. -/
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
  sorry

end AlbertsonBerman
