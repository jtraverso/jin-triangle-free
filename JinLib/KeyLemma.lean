/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.Patterns

/-!
# The key lemma

In a maximal triangle-free graph with `29 δ > 10 n`, every vertex is adjacent to some vertex of
every closed walk of length 5. The proof takes a counterexample `(a, U)` maximising
`|sSet G a U|`, moves it by a symmetry of the 5-cycle into one of eight normal forms, and applies
the corresponding case lemma of `JinLib.Patterns`.
-/

@[expose] public section

namespace DenseTriangleFree

open SimpleGraph

/-- The symmetries of the 5-cycle: `i ↦ r - i` or `i ↦ r + i`. -/
def sig (r : Fin 5) (s : Bool) (i : Fin 5) : Fin 5 := if s then r - i else r + i

lemma sig_step : ∀ (r : Fin 5) (s : Bool) (i : Fin 5),
    sig r s (i + 1) = sig r s i + 1 ∨ sig r s i = sig r s (i + 1) + 1 := by decide

lemma sig_nbrs : ∀ (r : Fin 5) (s : Bool) (i : Fin 5),
    (sig r s (i - 1) = sig r s i - 1 ∧ sig r s (i + 1) = sig r s i + 1) ∨
      (sig r s (i - 1) = sig r s i + 1 ∧ sig r s (i + 1) = sig r s i - 1) := by decide

lemma normal_form : ∀ S : Finset (Fin 5), ∃ r : Fin 5, ∃ s : Bool,
    (Finset.univ.filter fun i => sig r s i ∈ S).card = S.card ∧
    ((Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2, 3, 4} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2, 3} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 3} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 2} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = ∅) := by
  decide +kernel

variable {V : Type*} (G : SimpleGraph V)

lemma isPair_comp {a : V} {U : Fin 5 → V} (hp : IsPair G a U) (r : Fin 5) (s : Bool) :
    IsPair G a (U ∘ sig r s) := by
  refine ⟨fun i => ?_, fun i => hp.2 _⟩
  simp only [Function.comp]
  rcases sig_step r s i with h | h
  · rw [h]; exact hp.1 _
  · rw [h]; exact (hp.1 _).symm

lemma sSet_comp (a : V) (U : Fin 5 → V) (r : Fin 5) (s : Bool) :
    sSet G a (U ∘ sig r s) = Finset.univ.filter fun i => sig r s i ∈ sSet G a U := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_sSet, Function.comp]
  rcases sig_nbrs r s i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact ⟨fun ⟨t, h, h', h''⟩ => ⟨t, h, h'', h'⟩, fun ⟨t, h, h', h''⟩ => ⟨t, h, h'', h'⟩⟩

variable [Fintype V] [DecidableRel G.Adj]

/-- **Key lemma.** In a maximal triangle-free graph with `29 δ > 10 n`, every vertex is adjacent to
some vertex of every closed walk of length 5. -/
theorem key_lemma (h3 : G.CliqueFree 3)
    (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) (a : V) (U : Fin 5 → V)
    (hp : IsPair G a U) : False := by
  classical
  obtain ⟨p, hpmem, hpbest⟩ := Finset.exists_max_image
    (Finset.univ.filter fun p : V × (Fin 5 → V) => IsPair G p.1 p.2)
    (fun p => (sSet G p.1 p.2).card) ⟨(a, U), by simpa using hp⟩
  have hp0 : IsPair G p.1 p.2 := by simpa using hpmem
  have hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W →
      (sSet G b W).card ≤ (sSet G p.1 p.2).card :=
    fun b W h => hpbest (b, W) (by simpa using h)
  obtain ⟨r, s, hcard, hT⟩ := normal_form (sSet G p.1 p.2)
  have hp' := isPair_comp G hp0 r s
  rw [← sSet_comp] at hcard hT
  rw [← hcard] at hbest
  rcases hT with h | h | h | h | h | h | h | h <;> rw [h] at hbest <;>
    simp only [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_singleton, Finset.card_empty, or_self, not_false_eq_true,
      Fin.reduceEq] at hbest
  · exact patZ_01234_of G h3 hδ _ _ hp' h
  · exact patZ_0123_of G h3 hδ _ _ hp' h
  · exact patZ_012_of G h3 hδ hbest _ _ hp' h
  · exact patZ_013_of G h3 hmax hδ hbest _ _ hp' h
  · exact patZ_01_of G h3 hδ hbest _ _ hp' h
  · exact patZ_02_of G h3 hmax hδ hbest _ _ hp' h
  · exact patZ_0_of G h3 hmax hδ hbest _ _ hp' h
  · exact patZ_none_of G h3 hmax hδ hbest _ _ hp' h

end DenseTriangleFree
