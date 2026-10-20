/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.Jin

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `JinLib/` (namespace `DenseTriangleFree`). `Maximal.lean` reduces Jin's
theorem to maximal triangle-free graphs (any two distinct non-adjacent vertices have a common
neighbour). `KeyLemma.lean` and `Patterns.lean` prove the key lemma: in a maximal triangle-free
graph with `29 δ > 10 n` every vertex is adjacent to a vertex of every closed walk of length 5; an
extremal counterexample is reduced by the symmetries of the 5-cycle to eight patterns, each refuted
by maximality, by a weighted pigeonhole step (`Heavy.lean`, where `29 δ > 10 n` is used) or by
extremality, the last pattern being a homomorphic image of the Grötzsch graph, excluded by the
weights `3, 2, 4` (`Grotzsch.lean`). `Bipartite.lean` deduces that the non-neighbourhood of any
vertex has no odd closed walk, hence is bipartite, and gives the neighbourhood the third colour.
`Blowup.lean` builds the extremal blow-up of the Grötzsch graph for the sharpness statement.
-/

@[expose] public section

namespace JinTheorem

/-- **Jin's theorem (1995).** A finite triangle-free graph with `29 δ(G) > 10 n` is 3-colourable. -/
theorem jin {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 :=
  DenseTriangleFree.jin G h3 hδ

/-- **Sharpness (Häggkvist 1982).** For every `m ≥ 1` there is a triangle-free `10m`-regular graph
on `29m` vertices that is not 3-colourable. -/
theorem jin_sharp (m : ℕ) (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin (29 * m)), ∃ _ : DecidableRel G.Adj,
      G.CliqueFree 3 ∧ (∀ v, G.degree v = 10 * m) ∧ ¬ G.Colorable 3 :=
  DenseTriangleFree.jin_sharp m hm

end JinTheorem
