/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.Grotzsch

/-!
# Reduction to maximal triangle-free graphs

Every triangle-free graph on a finite vertex set is a spanning subgraph of a maximal triangle-free
graph; passing to it keeps the minimum-degree hypothesis of Jin's theorem, and a colouring of the
supergraph colours the original graph. In a maximal triangle-free graph any two distinct
non-adjacent vertices have a common neighbour.
-/

@[expose] public section

namespace DenseTriangleFree

open SimpleGraph

variable {V : Type*}

/-- Every triangle-free graph on a finite vertex set lies below a maximal triangle-free graph. -/
theorem exists_maximal_cliqueFree_three_le [Finite V] {G : SimpleGraph V} (h3 : G.CliqueFree 3) :
    ∃ G' : SimpleGraph V, G ≤ G' ∧ Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G' := by
  obtain ⟨G', hle, hmax⟩ :=
    (Set.toFinite {H : SimpleGraph V | H.CliqueFree 3}).exists_le_maximal (a := G) h3
  exact ⟨G', hle, hmax⟩

/-- In a maximal triangle-free graph, two distinct non-adjacent vertices have a common
neighbour. -/
theorem exists_common_neighbor_of_maximal {G : SimpleGraph V}
    (hG : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G) {u v : V} (huv : u ≠ v)
    (hnadj : ¬ G.Adj u v) : ∃ w, G.Adj u w ∧ G.Adj v w := by
  classical
  by_contra hno
  push Not at hno
  have hadj : ∀ x y, (G ⊔ edge u v).Adj x y →
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    intro x y h
    rcases (sup_adj _ _ _ _).mp h with h | h
    · exact Or.inl h
    · rw [edge_adj] at h
      tauto
  have hfree : (G ⊔ edge u v).CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
    have hab' := (G ⊔ edge u v).ne_of_adj hab
    have hac' := (G ⊔ edge u v).ne_of_adj hac
    have hbc' := (G ⊔ edge u v).ne_of_adj hbc
    rcases hadj _ _ hab with h1 | ⟨e1, e1'⟩ | ⟨e1, e1'⟩ <;>
    rcases hadj _ _ hac with h2 | ⟨e2, e2'⟩ | ⟨e2, e2'⟩ <;>
    rcases hadj _ _ hbc with h3 | ⟨e3, e3'⟩ | ⟨e3, e3'⟩ <;>
    subst_vars <;>
    first
      | exact triangle_of_cliqueFree hG.prop h1 h3 h2
      | exact hab' rfl | exact hac' rfl | exact hbc' rfl | exact huv rfl
      | exact hnadj ‹_› | exact hnadj (G.adj_symm ‹_›)
      | exact hno _ ‹_› ‹_›
      | exact hno _ ‹_› (G.adj_symm ‹_›)
      | exact hno _ (G.adj_symm ‹_›) ‹_›
      | exact hno _ (G.adj_symm ‹_›) (G.adj_symm ‹_›)
  have hle : G ⊔ edge u v ≤ G := hG.le_of_ge hfree le_sup_left
  exact hnadj (hle (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩)))

/-- **Step 0 of Jin's theorem.** It suffices to prove Jin's theorem for maximal triangle-free
graphs: if every maximal triangle-free graph `G'` on `V` with `29 δ(G') > 10 |V|` is 3-colourable,
then so is every triangle-free graph `G` on `V` with `29 δ(G) > 10 |V|`. -/
theorem jin_of_maximal [Fintype V]
    (hcore : ∀ G' : SimpleGraph V, [DecidableRel G'.Adj] →
      Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G' →
      10 * Fintype.card V < 29 * G'.minDegree → G'.Colorable 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.CliqueFree 3)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by
  classical
  obtain ⟨G', hle, hmax⟩ := exists_maximal_cliqueFree_three_le h3
  have hδ' : 10 * Fintype.card V < 29 * G'.minDegree :=
    lt_of_lt_of_le hδ (Nat.mul_le_mul_left _ (minDegree_le_minDegree hle))
  exact (hcore G' hmax hδ').mono_left hle

end DenseTriangleFree
