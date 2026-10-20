/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import JinLib.Grotzsch

/-!
# Häggkvist's blow-up of the Grötzsch graph

Weights `3m` on the outer cycle, `2m` on the inner vertices and `4m` on the centre.
-/

@[expose] public section

namespace DenseTriangleFree
open SimpleGraph

/-- Projection of the 29 weighted slots onto the Grötzsch graph. -/
def slotProj (k : Fin 29) : Fin 11 :=
  if k.val < 15 then ⟨k.val / 3, by omega⟩
  else if h : k.val < 25 then ⟨5 + (k.val - 15) / 2, by omega⟩ else 10

lemma slotProj_card : ∀ x : Fin 11,
    (Finset.univ.filter fun k : Fin 29 => grotzsch.Adj x (slotProj k)).card = 10 := by
  decide

/-- Projection of the blow-up onto the Grötzsch graph. -/
def blowProj (m : ℕ) (a : Fin (29 * m)) : Fin 11 := slotProj (finProdFinEquiv.symm a).1

/-- Häggkvist's blow-up of the Grötzsch graph. -/
def blowup (m : ℕ) : SimpleGraph (Fin (29 * m)) := grotzsch.comap (blowProj m)

instance (m : ℕ) : DecidableRel (blowup m).Adj := fun a b =>
  inferInstanceAs (Decidable (grotzsch.Adj (blowProj m a) (blowProj m b)))

lemma blowup_degree (m : ℕ) (a : Fin (29 * m)) : (blowup m).degree a = 10 * m := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  set x := blowProj m a
  have : (Finset.univ.filter fun b => (blowup m).Adj a b) =
      (Finset.univ.filter fun p : Fin 29 × Fin m => grotzsch.Adj x (slotProj p.1)).map
        finProdFinEquiv.toEmbedding := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
    simp [blowup, blowProj, x]
  rw [this, Finset.card_map]
  rw [show (Finset.univ.filter fun p : Fin 29 × Fin m => grotzsch.Adj x (slotProj p.1)) =
    (Finset.univ.filter fun k : Fin 29 => grotzsch.Adj x (slotProj k)) ×ˢ Finset.univ by
      ext p; simp]
  rw [Finset.card_product, slotProj_card]
  simp

lemma blowup_cliqueFree (m : ℕ) : (blowup m).CliqueFree 3 := by
  intro s hs
  classical
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
  exact grotzsch_triangle _ _ _ hab hbc hac

lemma blowup_not_colorable (m : ℕ) (hm : 0 < m) : ¬ (blowup m).Colorable 3 := by
  rintro ⟨c⟩
  apply grotzsch_not_colorable
  have sec : ∀ x : Fin 11, ∃ a : Fin (29 * m), blowProj m a = x := by
    intro x
    obtain ⟨k, hk⟩ : ∃ k : Fin 29, slotProj k = x := by revert x; decide
    exact ⟨finProdFinEquiv (k, ⟨0, hm⟩), by simp [blowProj, hk]⟩
  choose s hs using sec
  refine ⟨Coloring.mk (fun x => c (s x)) fun {x y} h => c.valid ?_⟩
  change grotzsch.Adj (blowProj m (s x)) (blowProj m (s y))
  rw [hs, hs]; exact h

end DenseTriangleFree
