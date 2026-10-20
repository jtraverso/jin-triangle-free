/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.KeyLemma

/-!
# Non-neighbourhoods are bipartite

Let `G` be a triangle-free graph in which any two distinct non-adjacent vertices have a common
neighbour, and in which every vertex is adjacent to some vertex of every closed walk of length 5
(by `key_lemma` this holds for maximal triangle-free graphs with `29 δ > 10 n`). Then for every
vertex `a` the subgraph induced on the non-neighbours of `a` contains no odd closed walk, hence is
bipartite; colouring the neighbourhood of `a` (an independent set) with a third colour gives a
proper 3-colouring of `G`.

Closed walks of length `m` are encoded as `m`-periodic sequences `c : ℕ → V`.
-/

@[expose] public section

namespace DenseTriangleFree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma succ_mod_cases (i L : ℕ) (hL : 0 < L) :
    (i % L + 1 < L ∧ (i + 1) % L = i % L + 1) ∨ (i % L + 1 = L ∧ (i + 1) % L = 0) := by
  have hlt := Nat.mod_lt i hL
  have hdiv : (i + 1) % L = (i % L + 1) % L := by
    conv_lhs => rw [← Nat.div_add_mod i L, add_assoc, Nat.mul_add_mod]
  rcases (by omega : i % L + 1 < L ∨ i % L + 1 = L) with h | h
  · exact Or.inl ⟨h, by rw [hdiv, Nat.mod_eq_of_lt h]⟩
  · exact Or.inr ⟨h, by rw [hdiv, h, Nat.mod_self]⟩

/-- Every vertex sees some vertex of a closed walk of length 5, stated with explicit vertices. -/
lemma adj_of_five
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i))
    (a w0 w1 w2 w3 w4 : V) (e0 : G.Adj w0 w1) (e1 : G.Adj w1 w2) (e2 : G.Adj w2 w3)
    (e3 : G.Adj w3 w4) (e4 : G.Adj w4 w0) :
    G.Adj a w0 ∨ G.Adj a w1 ∨ G.Adj a w2 ∨ G.Adj a w3 ∨ G.Adj a w4 := by
  obtain ⟨i, hi⟩ := hZ a ![w0, w1, w2, w3, w4] (fun i => by fin_cases i <;> assumption)
  fin_cases i <;> simp at hi <;> tauto

/-- A segment `c s, …, c (s + L - 1)` of a closed walk, closed up by an edge, is a closed walk. -/
lemma subwalk {a : V} {c : ℕ → V} (hc : ∀ i, G.Adj (c i) (c (i + 1)))
    (hn : ∀ i, ¬ G.Adj a (c i)) (s L : ℕ) (hL : 0 < L) (hch : G.Adj (c (s + L - 1)) (c s)) :
    (∀ i, c (s + (i + L) % L) = c (s + i % L)) ∧
    (∀ i, G.Adj (c (s + i % L)) (c (s + (i + 1) % L))) ∧ ∀ i, ¬ G.Adj a (c (s + i % L)) := by
  refine ⟨fun i => by rw [Nat.add_mod_right], fun i => ?_, fun i => hn _⟩
  rcases succ_mod_cases i L hL with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, ← add_assoc]; exact hc _
  · rw [h2, add_zero, show s + i % L = s + L - 1 by omega]; exact hch

/-- **No odd closed walk avoids the neighbourhood of a vertex.** -/
theorem no_odd_walk (h3 : G.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w)
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i))
    (a : V) (m : ℕ) : ∀ c : ℕ → V, (∀ i, c (i + m) = c i) → (∀ i, G.Adj (c i) (c (i + 1))) →
      (∀ i, ¬ G.Adj a (c i)) → Odd m → False := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c hper hc hn hodd
  have hodd' : m % 2 = 1 := Nat.odd_iff.1 hodd
  have short : ∀ s L, 0 < L → L < m → L % 2 = 1 → G.Adj (c (s + L - 1)) (c s) → False := by
    intro s L hL hLm hLo hch
    obtain ⟨h1, h2, h3'⟩ := subwalk hc hn s L hL hch
    exact ih L hLm _ h1 h2 h3' (Nat.odd_iff.2 hLo)
  have chord : ∀ s t, s + 2 ≤ t → t + 2 ≤ s + m → ¬ G.Adj (c s) (c t) := by
    intro s t hst htm hadj
    obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by omega⟩
    by_cases hd2 : d % 2 = 0
    · exact short s (d + 1) (by omega) (by omega) (by omega)
        (by rw [show s + (d + 1) - 1 = s + d by omega]; exact hadj.symm)
    · exact short (s + d) (m - d + 1) (by omega) (by omega) (by omega)
        (by rw [show s + d + (m - d + 1) - 1 = s + m by omega, hper]; exact hadj)
  have neq : ∀ s t, s < t → t < s + m → c s ≠ c t := by
    intro s t hst htm heq
    obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by omega⟩
    by_cases hd2 : d % 2 = 1
    · refine short s d (by omega) (by omega) hd2 ?_
      rw [heq]
      have := hc (s + d - 1)
      rwa [show s + d - 1 + 1 = s + d by omega] at this
    · refine short (s + d) (m - d) (by omega) (by omega) (by omega) ?_
      rw [← heq]
      have := hc (s + m - 1)
      rwa [show s + m - 1 + 1 = s + m by omega, hper,
        show s + m - 1 = s + d + (m - d) - 1 by omega] at this
  obtain rfl | rfl | rfl | hm7 : m = 1 ∨ m = 3 ∨ m = 5 ∨ 7 ≤ m := by omega
  · have h := hc 0
    rw [hper 0] at h
    exact G.irrefl h
  · have h := hc 2
    rw [show 2 + 1 = 0 + 3 from rfl, hper 0] at h
    exact triangle_of_cliqueFree' h3 (hc 0) (hc 1) h
  · have h := hc 4
    rw [show 4 + 1 = 0 + 5 from rfl, hper 0] at h
    rcases adj_of_five hZ a _ _ _ _ _ (hc 0) (hc 1) (hc 2) (hc 3) h with h | h | h | h | h <;>
      exact hn _ h
  obtain ⟨z, hz0, hz3⟩ := hcn (c 0) (c 3) (neq 0 3 (by omega) (by omega))
    (chord 0 3 (by omega) (by omega))
  have haz : G.Adj a z := by
    rcases adj_of_five hZ a _ _ _ _ _ (hc 0) (hc 1) (hc 2) hz3 hz0.symm with h | h | h | h | h
    all_goals first | exact h | exact absurd h (hn _)
  obtain rfl | hm9 : m = 7 ∨ 9 ≤ m := by omega
  · obtain ⟨z1, hz11, hz14⟩ := hcn (c 1) (c 4) (neq 1 4 (by omega) (by omega))
      (chord 1 4 (by omega) (by omega))
    have haz1 : G.Adj a z1 := by
      rcases adj_of_five hZ a _ _ _ _ _ (hc 1) (hc 2) (hc 3) hz14 hz11.symm with h | h | h | h | h
      all_goals first | exact h | exact absurd h (hn _)
    obtain ⟨z4, hz44, hz47⟩ := hcn (c 4) (c 7) (neq 4 7 (by omega) (by omega))
      (chord 4 7 (by omega) (by omega))
    have haz4 : G.Adj a z4 := by
      rcases adj_of_five hZ a _ _ _ _ _ (hc 4) (hc 5) (hc 6) hz47 hz44.symm with h | h | h | h | h
      all_goals first | exact h | exact absurd h (hn _)
    have hc2z4 : G.Adj (c 2) z4 := by
      rcases adj_of_five hZ (c 2) _ _ _ _ _ (hc 4) (hc 5) (hc 6) hz47 hz44.symm with
        h | h | h | h | h
      · exact absurd h (chord 2 4 (by omega) (by omega))
      · exact absurd h (chord 2 5 (by omega) (by omega))
      · exact absurd h (chord 2 6 (by omega) (by omega))
      · exact absurd h (chord 2 7 (by omega) (by omega))
      · exact h
    rcases adj_of_five hZ z _ _ _ _ _ hz11 hz14.symm hz44 hc2z4.symm (hc 1).symm with
      h | h | h | h | h
    · exact triangle_of_cliqueFree' h3 (hc 0) h.symm hz0.symm
    · exact triangle_of_cliqueFree' h3 haz h haz1.symm
    · exact triangle_of_cliqueFree' h3 (hc 3) h.symm hz3.symm
    · exact triangle_of_cliqueFree' h3 haz h haz4.symm
    · exact triangle_of_cliqueFree' h3 (hc 2) hz3 h
  · have hz5 : G.Adj (c 5) z := by
      rcases adj_of_five hZ (c 5) _ _ _ _ _ (hc 0) (hc 1) (hc 2) hz3 hz0.symm with
        h | h | h | h | h
      · exact absurd h.symm (chord 0 5 (by omega) (by omega))
      · exact absurd h.symm (chord 1 5 (by omega) (by omega))
      · exact absurd h.symm (chord 2 5 (by omega) (by omega))
      · exact absurd h.symm (chord 3 5 (by omega) (by omega))
      · exact h
    have hz6 : G.Adj (c 6) z := by
      rcases adj_of_five hZ (c 6) _ _ _ _ _ (hc 0) (hc 1) (hc 2) hz3 hz0.symm with
        h | h | h | h | h
      · exact absurd h.symm (chord 0 6 (by omega) (by omega))
      · exact absurd h.symm (chord 1 6 (by omega) (by omega))
      · exact absurd h.symm (chord 2 6 (by omega) (by omega))
      · exact absurd h.symm (chord 3 6 (by omega) (by omega))
      · exact h
    exact triangle_of_cliqueFree' h3 (hc 5) hz6 hz5.symm

/-- Under the hypotheses of `no_odd_walk`, `G` is 3-colourable. -/
theorem colorable_three_of_five (h3 : G.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w)
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i)) :
    G.Colorable 3 := by
  classical
  rcases isEmpty_or_nonempty V with hV | ⟨⟨a⟩⟩
  · exact ⟨Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v)⟩
  have h2 : (G.induce {v | ¬ G.Adj a v}).Colorable 2 := by
    rw [two_colorable_iff_forall_loop_even]
    intro u w
    rw [← Nat.not_odd_iff_even]
    intro hodd
    have hm : 0 < w.length := hodd.pos
    refine no_odd_walk h3 hcn hZ a w.length (fun k => (w.getVert (k % w.length)).val)
      (fun i => by simp only [Nat.add_mod_right]) (fun i => ?_)
      (fun i => (w.getVert (i % w.length)).prop) hodd
    have key : ∀ j < w.length, G.Adj (w.getVert j).val (w.getVert (j + 1)).val :=
      fun j hj => w.adj_getVert_succ hj
    rcases succ_mod_cases i w.length hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      exact key (i % w.length) (Nat.mod_lt i hm)
    · rw [h2]
      have := key (i % w.length) (Nat.mod_lt i hm)
      rw [h1, Walk.getVert_length] at this
      rwa [Walk.getVert_zero]
  obtain ⟨col⟩ := h2
  refine ⟨Coloring.mk (fun v => if h : G.Adj a v then 2 else (col ⟨v, h⟩).castSucc) ?_⟩
  intro u v huv
  by_cases hu : G.Adj a u <;> by_cases hv : G.Adj a v <;> simp only [hu, hv, dite_true, dite_false]
  · exact fun _ => triangle_of_cliqueFree' h3 hu huv hv.symm
  · generalize col ⟨v, hv⟩ = x
    revert x
    decide
  · generalize col ⟨u, hu⟩ = x
    revert x
    decide
  · intro h
    exact col.valid (show (G.induce {v | ¬ G.Adj a v}).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
      (Fin.castSucc_injective _ h)

/-- **Step 2 of Jin's theorem.** A maximal triangle-free graph with `29 δ > 10 n` is
3-colourable. -/
theorem colorable_of_maximal [Fintype V] [DecidableRel G.Adj]
    (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
    (hδ : 10 * Fintype.card V < 29 * G.minDegree) : G.Colorable 3 := by
  refine colorable_three_of_five hmax.prop
    (fun u v huv hn => exists_common_neighbor_of_maximal hmax huv hn) (fun a U hU => ?_)
  by_contra h
  push Not at h
  exact key_lemma G hmax.prop hmax hδ a U ⟨hU, h⟩

end DenseTriangleFree
