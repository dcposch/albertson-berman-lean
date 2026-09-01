# Albertson–Berman is false

Jung’s 31-vertex maximal planar seed \(T\) has induced-forest number
\(a(T)=15<16\), so a planar graph on \(n\) vertices need not contain an
induced forest of order \(n/2\). Albertson–Berman (1979) is therefore
false. This repository is a Lean 4 / Mathlib certificate of that seed:
a spherical triangulation (58 faces, two per edge, Euler characteristic 2)
and Jung’s selected-edge transfer \(a(T)\le a(X(B,Q))=15\). It does **not**
claim that 29 is the minimum order of a counterexample.

Source: Jung, *A 15/31 Counterexample Family to the Albertson–Berman
Conjecture*, [arXiv:2608.17350](https://arxiv.org/abs/2608.17350).

This is a Palomar project. Submissions go to
<https://submit.palomar-registry.org/>.

## Repository map

- `Challenge.lean` — audited statement `AlbertsonBerman.counterexample`.
- `Solution.lean` — the same declaration, proved.
- `AlbertsonBerman/` — sphere/BFS helpers, gadget cycle profile, transfer.
- `comparator.json`, `formalization.yaml` — Palomar metadata.

## Verify

```sh
lake build Challenge Solution AlbertsonBerman
printf 'import Solution\n#print axioms AlbertsonBerman.counterexample\n' \
  | lake env lean --stdin
```

Lean 4.32.0, Mathlib v4.32.0. Forbidden: `native_decide`, `Lean.ofReduceBool`.
Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
