/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.Blowup
public import JinLib.Maximal
public import JinLib.Bipartite

/-!
# Jin's theorem on dense triangle-free graphs

* `DenseTriangleFree.jin`: **Jin's theorem (1995).** A finite triangle-free graph on `n` vertices
  with minimum degree `δ > 10n/29` is 3-colourable.
* `DenseTriangleFree.jin_sharp`: the bound is sharp: for every `m ≥ 1` there is a triangle-free
  `10m`-regular graph on `29m` vertices that is not 3-colourable (Häggkvist's blow-up of the
  Grötzsch graph, with weights `3m` on the outer 5-cycle, `2m` on the inner vertices and `4m` on the
  centre).

This extends the case `r = 2` of the Andrásfai–Erdős–Sós theorem (`δ > 2n/5` forces bipartiteness),
which is in Mathlib as `SimpleGraph.colorable_of_cliqueFree_lt_minDegree`.
-/

@[expose] public section

namespace DenseTriangleFree

/-- **Jin's theorem (1995).** A finite triangle-free graph with `29 δ(G) > 10 n` is 3-colourable. -/
theorem jin {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by
  -- Step 0 (proved): reduce to maximal triangle-free graphs.
  refine jin_of_maximal ?_ G h3 hδ
  intro G' _ hmax hδ'
  -- Step 1 (`key_lemma`): every vertex of `G'` is adjacent to some vertex of every closed walk of
  -- length 5. The extremal case of its proof is a homomorphic image of the Grötzsch graph, excluded
  -- by the same weighting as in `minDegree_le_of_grotzsch_hom`.
  -- Step 2 (`colorable_of_maximal`): hence the non-neighbourhood of any vertex `a` has no odd
  -- closed walk, so it is bipartite, and the neighbourhood of `a` receives the third colour.
  exact colorable_of_maximal hmax hδ'

/-- **Sharpness (Häggkvist 1982).** For every `m ≥ 1` there is a triangle-free `10m`-regular graph
on `29m` vertices that is not 3-colourable. -/
theorem jin_sharp (m : ℕ) (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin (29 * m)), ∃ _ : DecidableRel G.Adj,
      G.CliqueFree 3 ∧ (∀ v, G.degree v = 10 * m) ∧ ¬ G.Colorable 3 :=
  ⟨blowup m, inferInstance, blowup_cliqueFree m, blowup_degree m, blowup_not_colorable m hm⟩

end DenseTriangleFree
