/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The Grötzsch graph

The Grötzsch graph on `Fin 11`: outer 5-cycle `u_i = i` (`i < 5`), inner vertices `v_i = 5 + i`
adjacent to `u_{i-1}` and `u_{i+1}`, and the centre `w = 10` adjacent to all `v_i`.
-/

@[expose] public section

namespace DenseTriangleFree

/-- Boolean adjacency of the Grötzsch graph. -/
def grotzschAdjB (i j : Fin 11) : Bool :=
  let a := i.val
  let b := j.val
  (a < 5 && b < 5 && ((a + 1) % 5 == b || (b + 1) % 5 == a)) ||
  (a < 5 && 5 ≤ b && b < 10 && ((b - 5 + 1) % 5 == a || (a + 1) % 5 == b - 5)) ||
  (b < 5 && 5 ≤ a && a < 10 && ((a - 5 + 1) % 5 == b || (b + 1) % 5 == a - 5)) ||
  (a == 10 && 5 ≤ b && b < 10) || (b == 10 && 5 ≤ a && a < 10)

lemma grotzschAdjB_symm : ∀ i j, grotzschAdjB i j = grotzschAdjB j i := by decide

lemma grotzschAdjB_irrefl : ∀ i, grotzschAdjB i i = false := by decide

/-- The Grötzsch graph. -/
def grotzsch : SimpleGraph (Fin 11) where
  Adj i j := grotzschAdjB i j = true
  symm := ⟨fun i j h => by rwa [grotzschAdjB_symm]⟩
  loopless := ⟨fun i h => by simp [grotzschAdjB_irrefl i] at h⟩

instance : DecidableRel grotzsch.Adj := fun i j =>
  inferInstanceAs (Decidable (grotzschAdjB i j = true))

/-- Weights `3` on the outer cycle, `2` on the inner vertices and `4` on the centre. -/
def grotzschWt (i : Fin 11) : ℕ := if i.val < 5 then 3 else if i.val < 10 then 2 else 4

lemma grotzsch_triangle (a b c : Fin 11) (hab : grotzsch.Adj a b) (hbc : grotzsch.Adj b c)
    (hac : grotzsch.Adj a c) : False := by
  revert a b c
  decide

lemma grotzsch_cliqueFree : grotzsch.CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
  exact grotzsch_triangle a b c hab hbc hac

set_option synthInstance.maxHeartbeats 1000000 in
-- The `Decidable` instance for the nested bounded quantifiers below is large.
set_option synthInstance.maxSize 100000 in
lemma grotzsch_not_colorable_aux : ∀ c0 c1 : Fin 3, c0 ≠ c1 → ∀ c2 : Fin 3, c1 ≠ c2 →
    ∀ c3 : Fin 3, c2 ≠ c3 → ∀ c4 : Fin 3, c3 ≠ c4 → c4 ≠ c0 →
    ∀ c5 : Fin 3, c5 ≠ c1 → c5 ≠ c4 → ∀ c6 : Fin 3, c6 ≠ c2 → c6 ≠ c0 →
    ∀ c7 : Fin 3, c7 ≠ c3 → c7 ≠ c1 → ∀ c8 : Fin 3, c8 ≠ c4 → c8 ≠ c2 →
    ∀ c9 : Fin 3, c9 ≠ c0 → c9 ≠ c3 →
    ∀ c10 : Fin 3, c10 ≠ c5 → c10 ≠ c6 → c10 ≠ c7 → c10 ≠ c8 → c10 ≠ c9 → False := by
  decide +kernel

/-- The Grötzsch graph is not 3-colourable. -/
theorem grotzsch_not_colorable : ¬ grotzsch.Colorable 3 := by
  rintro ⟨c⟩
  have h : ∀ i j : Fin 11, grotzschAdjB i j = true → c i ≠ c j := fun i j h => c.valid h
  exact grotzsch_not_colorable_aux (c 0) (c 1) (h 0 1 rfl) (c 2) (h 1 2 rfl) (c 3) (h 2 3 rfl)
    (c 4) (h 3 4 rfl) (h 4 0 rfl) (c 5) (h 5 1 rfl) (h 5 4 rfl) (c 6) (h 6 2 rfl) (h 6 0 rfl)
    (c 7) (h 7 3 rfl) (h 7 1 rfl) (c 8) (h 8 4 rfl) (h 8 2 rfl) (c 9) (h 9 0 rfl) (h 9 3 rfl)
    (c 10) (h 10 5 rfl) (h 10 6 rfl) (h 10 7 rfl) (h 10 8 rfl) (h 10 9 rfl)

/-- Boolean independence test for subsets of the Grötzsch graph. -/
def grotzschIndepB (b : Fin 11 → Bool) : Bool :=
  (List.finRange 11).all fun i => (List.finRange 11).all fun j =>
    !(grotzschAdjB i j && b i && b j)

/-- Weight of a subset of the Grötzsch graph given by a Boolean vector. -/
def grotzschWtB (b : Fin 11 → Bool) : ℕ :=
  ((List.finRange 11).map fun i => if b i then grotzschWt i else 0).sum

set_option maxRecDepth 100000 in
lemma grotzsch_indep_aux : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    grotzschIndepB ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] = true →
      grotzschWtB ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] ≤ 10 := by
  decide +kernel

/-- Every independent set of the Grötzsch graph has weight at most `10`. -/
theorem grotzsch_indep_weight (s : Fin 11 → Prop) [DecidablePred s]
    (hs : ∀ i j, grotzsch.Adj i j → s i → s j → False) :
    ∑ i, (if s i then grotzschWt i else 0) ≤ 10 := by
  have hb : ∀ b : Fin 11 → Bool, grotzschIndepB b = true → grotzschWtB b ≤ 10 := by
    intro b hb
    have := grotzsch_indep_aux (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10)
    have e : ![b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7, b 8, b 9, b 10] = b := by
      funext i; fin_cases i <;> rfl
    rw [e] at this
    exact this hb
  have h1 := hb (fun i => decide (s i)) (by
    simp only [grotzschIndepB, List.all_eq_true, List.mem_finRange, true_implies]
    intro i j
    by_cases h : grotzschAdjB i j = true
    · by_cases hi : s i
      · by_cases hj : s j
        · exact (hs i j h hi hj).elim
        · simp [hj]
      · simp [hi]
    · simp [h])
  have e : grotzschWtB (fun i => decide (s i)) = ∑ i, (if s i then grotzschWt i else 0) := by
    simp only [grotzschWtB, decide_eq_true_eq]
    rw [← Fin.sum_univ_def]
  omega

lemma grotzschWt_sum : ∑ i, grotzschWt i = 29 := by decide

lemma triangle_of_cliqueFree {V : Type*} {G : SimpleGraph V} (h3 : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) : False := by
  classical
  exact h3 {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

/-- **Weight lemma.** If a triangle-free graph `G` on `n` vertices receives a homomorphism from the
Grötzsch graph, then `29 δ(G) ≤ 10 n`. -/
theorem minDegree_le_of_grotzsch_hom {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.CliqueFree 3) (f : grotzsch →g G) :
    29 * G.minDegree ≤ 10 * Fintype.card V := by
  classical
  have key : ∀ y : V, ∑ x, (if G.Adj (f x) y then grotzschWt x else 0) ≤ 10 := by
    intro y
    apply grotzsch_indep_weight
    intro i j hij hi hj
    exact triangle_of_cliqueFree h3 (f.map_rel hij) hj hi
  calc 29 * G.minDegree = ∑ x, grotzschWt x * G.minDegree := by
        rw [← Finset.sum_mul, grotzschWt_sum]
    _ ≤ ∑ x, grotzschWt x * G.degree (f x) := by
        gcongr with x
        exact G.minDegree_le_degree _
    _ = ∑ x, ∑ y, (if G.Adj (f x) y then grotzschWt x else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
    _ = ∑ y, ∑ x, (if G.Adj (f x) y then grotzschWt x else 0) := Finset.sum_comm
    _ ≤ ∑ _y : V, 10 := Finset.sum_le_sum fun y _ => key y
    _ = 10 * Fintype.card V := by simp [mul_comm]

end DenseTriangleFree
