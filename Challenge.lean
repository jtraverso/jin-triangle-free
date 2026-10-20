/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Jin's theorem on dense triangle-free graphs

* `JinTheorem.jin`: **Jin's theorem (1995).** A finite triangle-free graph on `n` vertices
  with minimum degree `δ > 10n/29` is 3-colourable.
* `JinTheorem.jin_sharp`: the bound is sharp: for every `m ≥ 1` there is a triangle-free
  `10m`-regular graph on `29m` vertices that is not 3-colourable (Häggkvist's blow-up of the
  Grötzsch graph, with weights `3m` on the outer 5-cycle, `2m` on the inner vertices and `4m` on the
  centre).

This extends the case `r = 2` of the Andrásfai–Erdős–Sós theorem (`δ > 2n/5` forces bipartiteness),
which is in Mathlib as `SimpleGraph.colorable_of_cliqueFree_lt_minDegree`.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

namespace JinTheorem

/-- **Jin's theorem (1995).** A finite triangle-free graph with `29 δ(G) > 10 n` is 3-colourable. -/
theorem jin {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by
  sorry

/-- **Sharpness (Häggkvist 1982).** For every `m ≥ 1` there is a triangle-free `10m`-regular graph
on `29m` vertices that is not 3-colourable. -/
theorem jin_sharp (m : ℕ) (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin (29 * m)), ∃ _ : DecidableRel G.Adj,
      G.CliqueFree 3 ∧ (∀ v, G.degree v = 10 * m) ∧ ¬ G.Colorable 3 := by
  sorry

end JinTheorem
