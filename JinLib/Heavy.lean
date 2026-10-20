/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.Grotzsch

/-!
# Weighted pigeonhole for dense triangle-free graphs

If `29 δ(G) > 10 n` and `x₀, …, x_{k-1}` are vertices carrying weights `w₀, …, w_{k-1}`, then some
vertex `y` is adjacent to a set of the `xᵢ` of weight more than `10/29` of the total. In a
triangle-free graph that set is independent with respect to every known edge among the `xᵢ`.
`heavy_step` packages this together with a verified enumeration of independent sets, so that a
finite case analysis on the neighbourhood of `y` can be discharged by `decide`.
-/

@[expose] public section

namespace DenseTriangleFree

open SimpleGraph

/-! ### The enumeration of independent sets -/

/-- Enumerate all subsets `s` of `vs` that are independent for `E` (together with the already
chosen list `ch`) and check `P (s ++ ch)` for each of them. -/
def enumIndep (E : ℕ → ℕ → Bool) (P : List ℕ → Bool) : List ℕ → List ℕ → Bool
  | [], ch => P ch
  | v :: vs, ch => enumIndep E P vs ch && (ch.any (E v) || enumIndep E P vs (v :: ch))

theorem enumIndep_sound (E : ℕ → ℕ → Bool) (P : List ℕ → Bool)
    (hP : ∀ l l' : List ℕ, l.Perm l' → P l = P l') (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ i j, q i → q j → E i j = false) :
    ∀ vs ch : List ℕ, (∀ j ∈ ch, q j) → enumIndep E P vs ch = true →
      P (vs.filter (fun i => decide (q i)) ++ ch) = true := by
  intro vs
  induction vs with
  | nil => intro ch _ h; simpa [enumIndep] using h
  | cons v vs ih =>
    intro ch hch h
    simp only [enumIndep, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    by_cases hv : q v
    · have hany : ch.any (E v) = false := by
        rw [List.any_eq_false]
        intro j hj
        simp [hq v j hv (hch j hj)]
      rcases h2 with h2 | h2
      · rw [hany] at h2; exact absurd h2 (by simp)
      have := ih (v :: ch) (by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hv
        · exact hch j hj) h2
      rw [List.filter_cons_of_pos (by simpa using hv)]
      rw [List.cons_append, ← hP _ _ List.perm_middle]
      exact this
    · rw [List.filter_cons_of_neg (by simpa using hv)]
      exact ih ch hch h1

/-- Symmetric adjacency test from a list of edges. -/
def edgeFn (edges : List (ℕ × ℕ)) (i j : ℕ) : Bool :=
  edges.any fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)

/-- Weight of a list of indices. -/
def wsumL (ws : List ℕ) (l : List ℕ) : ℕ := (l.map fun i => ws.getD i 0).sum

/-- The test applied to each independent set: it is light, or contains a forbidden set, or
contains one of the sets in `Js`. -/
def heavyTest (ws : List ℕ) (Fb Js : List (List ℕ)) (l : List ℕ) : Bool :=
  Nat.ble (29 * wsumL ws l) (10 * ws.sum) || Fb.any (fun F => F.all fun i => l.elem i) ||
    Js.any (fun J => J.all fun i => l.elem i)

theorem heavyTest_perm (ws : List ℕ) (Fb Js : List (List ℕ)) (l l' : List ℕ) (h : l.Perm l') :
    heavyTest ws Fb Js l = heavyTest ws Fb Js l' := by
  have hs : wsumL ws l = wsumL ws l' := (h.map _).sum_eq
  have hm : ∀ i, l.elem i = l'.elem i := by
    intro i
    rw [Bool.eq_iff_iff]
    simp only [List.elem_iff]
    exact h.mem_iff
  simp only [heavyTest, hs, hm]

/-- The full check: every independent heavy set avoiding the forbidden sets contains a member of
`Js`. -/
def heavyCheck (ws : List ℕ) (edges : List (ℕ × ℕ)) (Fb Js : List (List ℕ)) : Bool :=
  enumIndep (edgeFn edges) (heavyTest ws Fb Js) ((List.range ws.length).filter fun i =>
    0 < ws.getD i 0) []

/-! ### Weighted pigeonhole -/

section Pigeonhole

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_heavy_vertex (hδ : 10 * Fintype.card V < 29 * G.minDegree) {k : ℕ}
    (f : ℕ → V) (w : ℕ → ℕ) (hpos : 0 < ∑ i ∈ Finset.range k, w i) :
    ∃ y, 10 * ∑ i ∈ Finset.range k, w i <
      29 * ∑ i ∈ Finset.range k, (if G.Adj (f i) y then w i else 0) := by
  by_contra hno
  push Not at hno
  have key : (∑ i ∈ Finset.range k, w i) * (29 * G.minDegree) ≤
      (∑ i ∈ Finset.range k, w i) * (10 * Fintype.card V) := by
    calc (∑ i ∈ Finset.range k, w i) * (29 * G.minDegree)
        = 29 * ∑ i ∈ Finset.range k, w i * G.minDegree := by
          rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ 29 * ∑ i ∈ Finset.range k, w i * G.degree (f i) := by
          gcongr with i
          exact G.minDegree_le_degree _
      _ = 29 * ∑ i ∈ Finset.range k, ∑ y, (if G.Adj (f i) y then w i else 0) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          split_ifs <;> simp
      _ = ∑ y, 29 * ∑ i ∈ Finset.range k, (if G.Adj (f i) y then w i else 0) := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ _y : V, 10 * ∑ i ∈ Finset.range k, w i := Finset.sum_le_sum fun y _ => hno y
      _ = (∑ i ∈ Finset.range k, w i) * (10 * Fintype.card V) := by
          simp [Finset.card_univ]; ring
  have := le_of_mul_le_mul_left key hpos
  omega

end Pigeonhole

theorem triangle_of_cliqueFree' {V : Type*} {G : SimpleGraph V} (h3 : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False :=
  triangle_of_cliqueFree h3 hab hbc hca.symm

lemma listsum_range (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma sum_map_filter' {p : ℕ → Prop} [DecidablePred p] (L : List ℕ) (g : ℕ → ℕ) :
    ((L.filter fun i => decide (p i)).map g).sum =
      (L.map fun i => if p i then g i else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases h : p a <;> simp [h, ih]

lemma list_sum_eq_range (ws : List ℕ) : ws.sum = ∑ i ∈ Finset.range ws.length, ws.getD i 0 := by
  induction ws with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ih]; simp [add_comm]

lemma wsumL_filter (ws : List ℕ) (q : ℕ → Prop) [DecidablePred q] :
    wsumL ws (((List.range ws.length).filter fun i => 0 < ws.getD i 0).filter
      (fun i => decide (q i))) =
      ∑ i ∈ Finset.range ws.length, (if q i then ws.getD i 0 else 0) := by
  unfold wsumL
  rw [sum_map_filter', ← listsum_range]
  have := sum_map_filter' (p := fun i => 0 < ws.getD i 0) (List.range ws.length)
    (fun i => if q i then ws.getD i 0 else 0)
  rw [this]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs <;> omega

/-- **Heavy step.** In a triangle-free graph with `29 δ > 10 n`, for vertices `f i` with weights
`ws`, known edges `edges` and forbidden sets `Fb` (no vertex sees all of a forbidden set), if the
check succeeds then some vertex sees all of some `J ∈ Js`. -/
theorem heavy_step {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h3 : G.CliqueFree 3) (hδ : 10 * Fintype.card V < 29 * G.minDegree)
    (f : ℕ → V) (ws : List ℕ) (edges : List (ℕ × ℕ)) (Fb Js : List (List ℕ))
    (hE : ∀ e ∈ edges, G.Adj (f e.1) (f e.2))
    (hF : ∀ F ∈ Fb, ∀ y, (∀ i ∈ F, G.Adj (f i) y) → False)
    (hpos : 0 < ws.sum)
    (hc : heavyCheck ws edges Fb Js = true) :
    ∃ J ∈ Js, ∃ y, ∀ i ∈ J, G.Adj (f i) y := by
  classical
  have hpos' : 0 < ∑ i ∈ Finset.range ws.length, ws.getD i 0 := by
    rwa [← list_sum_eq_range]
  obtain ⟨y, hy⟩ := exists_heavy_vertex G hδ f (fun i => ws.getD i 0) hpos'
  have hsound := enumIndep_sound (edgeFn edges) (heavyTest ws Fb Js) (heavyTest_perm ws Fb Js)
    (fun i => G.Adj (f i) y) (by
      intro i j hi hj
      by_contra hne
      simp only [edgeFn, Bool.not_eq_false, List.any_eq_true, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hne
      obtain ⟨e, he, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := hne
      · have := hE e he
        rw [h1, h2] at this
        exact triangle_of_cliqueFree' h3 this hj hi.symm
      · have := hE e he
        rw [h1, h2] at this
        exact triangle_of_cliqueFree' h3 this hi hj.symm)
    _ [] (by simp) hc
  rw [List.append_nil] at hsound
  simp only [heavyTest, Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at hsound
  rw [wsumL_filter] at hsound
  rcases hsound with (hl | ⟨F, hF', hFall⟩) | ⟨J, hJ, hJall⟩
  · rw [list_sum_eq_range] at hl
    have := Nat.le_of_ble_eq_true hl
    omega
  · exfalso
    refine hF F hF' y fun i hi => ?_
    have := hFall i hi
    simp only [List.elem_iff, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  · refine ⟨J, hJ, y, fun i hi => ?_⟩
    have := hJall i hi
    simp only [List.elem_iff, List.mem_filter, decide_eq_true_eq] at this
    exact this.2

end DenseTriangleFree
