/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.Pairs
public import JinLib.Maximal

/-!
# The eight cases of the key lemma

Let `(a, U)` be a pair (`a` adjacent to no vertex of the 5-cycle `U = x1 x2 x3 x4 x5`, with
`a = x0`) maximising `m = |sSet G a U|`. Up to the symmetries of the 5-cycle, `sSet G a U` is one
of `{0,1,2,3,4}`, `{0,1,2,3}`, `{0,1,2}`, `{0,1,3}`, `{0,1}`, `{0,2}`, `{0}` and `∅`; for
`j ∈ sSet` the vertex `v_j` is a common neighbour of `a`, `U (j-1)` and `U (j+1)`, and for
`j ∉ sSet` no such vertex exists (hypotheses `fj`). Each theorem below derives a contradiction in
one case, using only three kinds of steps:

* maximality: two distinct non-adjacent vertices have a common neighbour;
* the weighted pigeonhole principle `heavy_step` (this is where `29 δ > 10 n` enters): for
  suitable weights some vertex sees more than `10/29` of the total weight; the possible
  neighbourhoods are enumerated by `decide`;
* `pair_contra`: a pair with more than `m` witnessed indices contradicts the choice of `(a, U)`.

When `sSet = Fin 5` the configuration is a homomorphic image of the Grötzsch graph and the first
step is already contradictory.
-/

@[expose] public section

namespace DenseTriangleFree

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (h3 : G.CliqueFree 3) (hmax : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G)
  (hδ : 10 * Fintype.card V < 29 * G.minDegree)

include h3 hmax hδ

omit hmax in
theorem patZ_01234 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : V) (h_1_2 : G.Adj x1 x2)
    (h_2_3 : G.Adj x2 x3) (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1)
    (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6) (h_0_7 : G.Adj x0 x7)
    (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8) (h_2_8 : G.Adj x2 x8)
    (h_4_8 : G.Adj x4 x8) (h_0_9 : G.Adj x0 x9) (h_3_9 : G.Adj x3 x9) (h_5_9 : G.Adj x5 x9)
    (h_0_10 : G.Adj x0 x10) (h_4_10 : G.Adj x4 x10) (h_1_10 : G.Adj x1 x10) :
    False := by
  obtain ⟨J, hJ, x11, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10].getD i x0)
    [4, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2]
    [(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 2), (1, 7), (1, 10), (2, 3), (2, 6), (2, 8),
     (3, 4), (3, 7), (3, 9), (4, 5), (4, 8), (4, 10), (5, 1), (5, 6), (5, 9)]
    []
    []
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_0_10, h_1_2, h_1_7, h_1_10, h_2_3, h_2_6, h_2_8,
             h_3_4, h_3_7, h_3_9, h_4_5, h_4_8, h_4_10, h_5_1, h_5_6, h_5_9⟩)
    (by intro F hF; simp at hF)
    (by decide) (by decide +kernel)
  simp at hJ

omit hmax in
theorem patZ_01234_of
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1, 2, 3, 4} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 1, 2, 3, 4} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v1, hv1a, hv1b, hv1c⟩ := hin 1 (by decide)
  obtain ⟨v2, hv2a, hv2b, hv2c⟩ := hin 2 (by decide)
  obtain ⟨v3, hv3a, hv3b, hv3c⟩ := hin 3 (by decide)
  obtain ⟨v4, hv4a, hv4b, hv4c⟩ := hin 4 (by decide)
  exact patZ_01234 G h3 hδ a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v1 v2 v3 v4 (hU 0) (hU 1) (hU 2)
    (hU 3) (hU 4) hv0a hv0b hv0c hv1a hv1b hv1c hv2a hv2b hv2c hv3a hv3b hv3c hv4a hv4b hv4c

omit hmax in
theorem patZ_0123 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (h_0_6 : G.Adj x0 x6)
    (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6) (h_0_7 : G.Adj x0 x7) (h_1_7 : G.Adj x1 x7)
    (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8) (h_2_8 : G.Adj x2 x8) (h_4_8 : G.Adj x4 x8)
    (h_0_9 : G.Adj x0 x9) (h_3_9 : G.Adj x3 x9) (h_5_9 : G.Adj x5 x9)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨J, hJ, x10, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD i x0)
    [1, 1, 0, 0, 1, 1, 0, 1, 1, 0]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (2, 8), (3, 4), (3, 7),
     (3, 9), (4, 5), (4, 8), (5, 1), (5, 6), (5, 9)]
    [[0, 4, 1]]
    [[5, 7, 8]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_2_8, h_3_4, h_3_7, h_3_9,
             h_4_5, h_4_8, h_5_1, h_5_6, h_5_9⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_5_10 : G.Adj x5 x10 := hx 5 (by simp)
  have h_7_10 : G.Adj x7 x10 := hx 7 (by simp)
  have h_8_10 : G.Adj x8 x10 := hx 8 (by simp)
  obtain ⟨J, hJ, x11, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10].getD i x0)
    [3, 2, 3, 3, 2, 4, 2, 3, 3, 2, 2]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (2, 8), (3, 4), (3, 7),
     (3, 9), (4, 5), (4, 8), (5, 1), (5, 6), (5, 9), (5, 10), (7, 10), (8, 10)]
    [[0, 4, 1]]
    []
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_2_8, h_3_4, h_3_7, h_3_9,
             h_4_5, h_4_8, h_5_1, h_5_6, h_5_9, h_5_10, h_7_10, h_8_10⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      subst hF
      exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp at hJ

omit hmax in
theorem patZ_0123_of
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1, 2, 3} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 1, 2, 3} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  have hout : ∀ j, j ∉ ({0, 1, 2, 3} : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v1, hv1a, hv1b, hv1c⟩ := hin 1 (by decide)
  obtain ⟨v2, hv2a, hv2b, hv2c⟩ := hin 2 (by decide)
  obtain ⟨v3, hv3a, hv3b, hv3c⟩ := hin 3 (by decide)
  exact patZ_0123 G h3 hδ a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v1 v2 v3 (hU 0) (hU 1) (hU 2)
    (hU 3) (hU 4) hv0a hv0b hv0c hv1a hv1b hv1c hv2a hv2b hv2c hv3a hv3b hv3c
    (hout 4 (by decide))

omit hmax in
theorem patZ_012 (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_4 : ¬ G.Adj x0 x4)
    (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6) (h_0_7 : G.Adj x0 x7)
    (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8) (h_2_8 : G.Adj x2 x8)
    (h_4_8 : G.Adj x4 x8) (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨J, hJ, x9, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8].getD i x0)
    [1, 0, 0, 1, 1, 1, 1, 1, 0]
    [(0, 6), (0, 7), (0, 8), (1, 2), (1, 7), (2, 3), (2, 6), (2, 8), (3, 4), (3, 7), (4, 5),
     (4, 8), (5, 1), (5, 6)]
    [[0, 3, 5], [0, 4, 1]]
    [[4, 6, 7]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_1_2, h_1_7, h_2_3, h_2_6, h_2_8, h_3_4, h_3_7, h_4_5, h_4_8,
             h_5_1, h_5_6⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_4_9 : G.Adj x4 x9 := hx 4 (by simp)
  have h_6_9 : G.Adj x6 x9 := hx 6 (by simp)
  have h_7_9 : G.Adj x7 x9 := hx 7 (by simp)
  exact pair_contra G hbest x4 x0 x6 x2 x1 x7
    h_0_6 h_2_6.symm h_1_2.symm h_1_7 h_0_7.symm
    (fun h : G.Adj x4 x0 => n_0_4 h.symm)
    (fun h : G.Adj x4 x6 => triangle_of_cliqueFree' h3 h_4_5 h_5_6 h.symm)
    (fun h : G.Adj x4 x2 => triangle_of_cliqueFree' h3 h_2_3 h_3_4 h)
    (fun h : G.Adj x4 x1 => triangle_of_cliqueFree' h3 h_5_1.symm h_4_5.symm h)
    (fun h : G.Adj x4 x7 => triangle_of_cliqueFree' h3 h_3_4.symm h_3_7 h.symm)
    {0, 1, 2, 3} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x9, h_4_9, h_7_9, h_6_9⟩
      · exact ⟨x8, h_4_8, h_0_8, h_2_8⟩
      · exact ⟨x5, h_4_5, h_5_6.symm, h_5_1.symm⟩
      · exact ⟨x3, h_3_4.symm, h_2_3, h_3_7.symm⟩)

omit hmax in
theorem patZ_012_of
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1, 2} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 1, 2} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  have hout : ∀ j, j ∉ ({0, 1, 2} : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v1, hv1a, hv1b, hv1c⟩ := hin 1 (by decide)
  obtain ⟨v2, hv2a, hv2b, hv2c⟩ := hin 2 (by decide)
  exact patZ_012 G h3 hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v1 v2 (hU 0) (hU 1) (hU 2)
    (hU 3) (hU 4) (hn 3) hv0a hv0b hv0c hv1a hv1b hv1c hv2a hv2b hv2c (hout 3 (by decide))
    (hout 4 (by decide))

theorem patZ_013 (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_3 : ¬ G.Adj x0 x3)
    (n_0_4 : ¬ G.Adj x0 x4) (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6)
    (h_0_7 : G.Adj x0 x7) (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7) (h_0_8 : G.Adj x0 x8)
    (h_3_8 : G.Adj x3 x8) (h_5_8 : G.Adj x5 x8)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨x9, h_0_9, h_4_9⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x4 => (fun h : G.Adj x3 x0 => n_0_3 h.symm) (by rw [h]; exact h_3_4))
    n_0_4
  obtain ⟨J, hJ, x10, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD i x0)
    [1, 0, 1, 1, 1, 0, 1, 0, 0, 1]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (3, 4), (3, 7), (3, 8),
     (4, 5), (4, 9), (5, 1), (5, 6), (5, 8)]
    [[0, 2, 4], [0, 4, 1]]
    [[3, 6, 9]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_3_4, h_3_7, h_3_8, h_4_5,
             h_4_9, h_5_1, h_5_6, h_5_8⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_3_10 : G.Adj x3 x10 := hx 3 (by simp)
  have h_6_10 : G.Adj x6 x10 := hx 6 (by simp)
  have h_9_10 : G.Adj x9 x10 := hx 9 (by simp)
  obtain ⟨J, hJ, x11, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10].getD i x0)
    [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]
    [(0, 6), (0, 7), (0, 8), (0, 9), (1, 2), (1, 7), (2, 3), (2, 6), (3, 4), (3, 7), (3, 8),
     (3, 10), (4, 5), (4, 9), (5, 1), (5, 6), (5, 8), (6, 10), (9, 10)]
    [[0, 2, 4], [0, 4, 1]]
    [[5, 7, 9]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_0_9, h_1_2, h_1_7, h_2_3, h_2_6, h_3_4, h_3_7, h_3_8,
             h_3_10, h_4_5, h_4_9, h_5_1, h_5_6, h_5_8, h_6_10, h_9_10⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_5_11 : G.Adj x5 x11 := hx 5 (by simp)
  have h_7_11 : G.Adj x7 x11 := hx 7 (by simp)
  have h_9_11 : G.Adj x9 x11 := hx 9 (by simp)
  exact pair_contra G hbest x3 x0 x6 x5 x11 x9
    h_0_6 h_5_6.symm h_5_11 h_9_11.symm h_0_9.symm
    (fun h : G.Adj x3 x0 => n_0_3 h.symm)
    (fun h : G.Adj x3 x6 => triangle_of_cliqueFree' h3 h_2_3.symm h_2_6 h.symm)
    (fun h : G.Adj x3 x5 => triangle_of_cliqueFree' h3 h_3_4 h_4_5 h.symm)
    (fun h : G.Adj x3 x11 => triangle_of_cliqueFree' h3 h_3_7 h_7_11 h.symm)
    (fun h : G.Adj x3 x9 => triangle_of_cliqueFree' h3 h_3_4 h_4_9 h.symm)
    {0, 1, 3, 4} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x10, h_3_10, h_9_10, h_6_10⟩
      · exact ⟨x8, h_3_8, h_0_8, h_5_8⟩
      · exact ⟨x4, h_3_4, h_4_5.symm, h_4_9.symm⟩
      · exact ⟨x7, h_3_7, h_7_11.symm, h_0_7⟩)

theorem patZ_013_of
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 3)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1, 3} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 1, 3} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  have hout : ∀ j, j ∉ ({0, 1, 3} : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v1, hv1a, hv1b, hv1c⟩ := hin 1 (by decide)
  obtain ⟨v3, hv3a, hv3b, hv3c⟩ := hin 3 (by decide)
  exact patZ_013 G h3 hmax hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v1 v3 (hU 0) (hU 1)
    (hU 2) (hU 3) (hU 4) (hn 2) (hn 3) hv0a hv0b hv0c hv1a hv1b hv1c hv3a hv3b hv3c
    (hout 2 (by decide)) (hout 4 (by decide))

omit hmax in
theorem patZ_01 (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 2)
    (x0 x1 x2 x3 x4 x5 x6 x7 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_4 : ¬ G.Adj x0 x4)
    (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6) (h_0_7 : G.Adj x0 x7)
    (h_1_7 : G.Adj x1 x7) (h_3_7 : G.Adj x3 x7)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨J, hJ, x8, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7].getD i x0)
    [1, 0, 0, 1, 1, 1, 1, 1]
    [(0, 6), (0, 7), (1, 2), (1, 7), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (5, 1), (5, 6)]
    [[0, 2, 4], [0, 3, 5], [0, 4, 1]]
    [[4, 6, 7]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_1_2, h_1_7, h_2_3, h_2_6, h_3_4, h_3_7, h_4_5, h_5_1, h_5_6⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_4_8 : G.Adj x4 x8 := hx 4 (by simp)
  have h_6_8 : G.Adj x6 x8 := hx 6 (by simp)
  have h_7_8 : G.Adj x7 x8 := hx 7 (by simp)
  exact pair_contra G hbest x4 x0 x6 x2 x1 x7
    h_0_6 h_2_6.symm h_1_2.symm h_1_7 h_0_7.symm
    (fun h : G.Adj x4 x0 => n_0_4 h.symm)
    (fun h : G.Adj x4 x6 => triangle_of_cliqueFree' h3 h_4_5 h_5_6 h.symm)
    (fun h : G.Adj x4 x2 => triangle_of_cliqueFree' h3 h_2_3 h_3_4 h)
    (fun h : G.Adj x4 x1 => triangle_of_cliqueFree' h3 h_5_1.symm h_4_5.symm h)
    (fun h : G.Adj x4 x7 => triangle_of_cliqueFree' h3 h_3_4.symm h_3_7 h.symm)
    {0, 2, 3} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x8, h_4_8, h_7_8, h_6_8⟩
      · exact ⟨x5, h_4_5, h_5_6.symm, h_5_1.symm⟩
      · exact ⟨x3, h_3_4.symm, h_2_3, h_3_7.symm⟩)

omit hmax in
theorem patZ_01_of
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 2)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 1} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 1} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  have hout : ∀ j, j ∉ ({0, 1} : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v1, hv1a, hv1b, hv1c⟩ := hin 1 (by decide)
  exact patZ_01 G h3 hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v1 (hU 0) (hU 1) (hU 2) (hU 3)
    (hU 4) (hn 3) hv0a hv0b hv0c hv1a hv1b hv1c (hout 2 (by decide)) (hout 3 (by decide))
    (hout 4 (by decide))

theorem patZ_02 (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 2)
    (x0 x1 x2 x3 x4 x5 x6 x7 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3)
    (h_3_4 : G.Adj x3 x4) (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_1 : ¬ G.Adj x0 x1)
    (n_0_2 : ¬ G.Adj x0 x2) (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6) (h_2_6 : G.Adj x2 x6)
    (h_0_7 : G.Adj x0 x7) (h_2_7 : G.Adj x2 x7) (h_4_7 : G.Adj x4 x7)
    (f1 : ∀ t, G.Adj x0 t → G.Adj x1 t → G.Adj x3 t → False)
    (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨x8, h_0_8, h_1_8⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x1 => (fun h : G.Adj x2 x0 => n_0_2 h.symm) (by rw [h]; exact h_1_2.symm))
    n_0_1
  obtain ⟨J, hJ, x9, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8].getD i x0)
    [1, 1, 0, 0, 1, 1, 0, 1, 1]
    [(0, 6), (0, 7), (0, 8), (1, 2), (1, 8), (2, 3), (2, 6), (2, 7), (3, 4), (4, 5), (4, 7),
     (5, 1), (5, 6)]
    [[0, 1, 3], [0, 3, 5], [0, 4, 1]]
    [[5, 7, 8]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_1_2, h_1_8, h_2_3, h_2_6, h_2_7, h_3_4, h_4_5, h_4_7, h_5_1,
             h_5_6⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl
      · exact f1 y (hy 0 (by simp)) (hy 1 (by simp)) (hy 3 (by simp))
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_5_9 : G.Adj x5 x9 := hx 5 (by simp)
  have h_7_9 : G.Adj x7 x9 := hx 7 (by simp)
  have h_8_9 : G.Adj x8 x9 := hx 8 (by simp)
  exact pair_contra G hbest x8 x2 x6 x5 x4 x7
    h_2_6 h_5_6.symm h_4_5.symm h_4_7 h_2_7.symm
    (fun h : G.Adj x8 x2 => triangle_of_cliqueFree' h3 h_1_2.symm h_1_8 h)
    (fun h : G.Adj x8 x6 => triangle_of_cliqueFree' h3 h_0_6.symm h_0_8 h)
    (fun h : G.Adj x8 x5 => triangle_of_cliqueFree' h3 h_5_1 h_1_8 h)
    (fun h : G.Adj x8 x4 => f4 x8 h_0_8 h.symm h_1_8)
    (fun h : G.Adj x8 x7 => triangle_of_cliqueFree' h3 h_0_7.symm h_0_8 h)
    {0, 1, 3} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x0, h_0_8.symm, h_0_7.symm, h_0_6.symm⟩
      · exact ⟨x1, h_1_8.symm, h_1_2.symm, h_5_1⟩
      · exact ⟨x9, h_8_9, h_5_9, h_7_9⟩)

theorem patZ_02_of
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 2)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0, 2} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0, 2} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  have hout : ∀ j, j ∉ ({0, 2} : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  obtain ⟨v2, hv2a, hv2b, hv2c⟩ := hin 2 (by decide)
  exact patZ_02 G h3 hmax hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) v0 v2 (hU 0) (hU 1) (hU 2)
    (hU 3) (hU 4) (hn 0) (hn 1) hv0a hv0b hv0c hv2a hv2b hv2c (hout 1 (by decide))
    (hout 3 (by decide)) (hout 4 (by decide))

theorem patZ_0 (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 1)
    (x0 x1 x2 x3 x4 x5 x6 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3) (h_3_4 : G.Adj x3 x4)
    (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_2 : ¬ G.Adj x0 x2) (n_0_3 : ¬ G.Adj x0 x3)
    (n_0_4 : ¬ G.Adj x0 x4) (n_0_5 : ¬ G.Adj x0 x5) (h_0_6 : G.Adj x0 x6) (h_5_6 : G.Adj x5 x6)
    (h_2_6 : G.Adj x2 x6) (f1 : ∀ t, G.Adj x0 t → G.Adj x1 t → G.Adj x3 t → False)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨x7, h_0_7, h_3_7⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x3 => (fun h : G.Adj x2 x0 => n_0_2 h.symm) (by rw [h]; exact h_2_3))
    n_0_3
  obtain ⟨x8, h_0_8, h_4_8⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x4 => (fun h : G.Adj x3 x0 => n_0_3 h.symm) (by rw [h]; exact h_3_4))
    n_0_4
  obtain ⟨J, hJ, x9, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8].getD i x0)
    [1, 0, 1, 1, 1, 0, 1, 0, 1]
    [(0, 6), (0, 7), (0, 8), (1, 2), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (4, 8), (5, 1),
     (5, 6)]
    [[0, 1, 3], [0, 2, 4], [0, 3, 5], [0, 4, 1]]
    [[3, 6, 8]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_1_2, h_2_3, h_2_6, h_3_4, h_3_7, h_4_5, h_4_8, h_5_1,
             h_5_6⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl | rfl
      · exact f1 y (hy 0 (by simp)) (hy 1 (by simp)) (hy 3 (by simp))
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  subst hJ
  have h_3_9 : G.Adj x3 x9 := hx 3 (by simp)
  have h_6_9 : G.Adj x6 x9 := hx 6 (by simp)
  have h_8_9 : G.Adj x8 x9 := hx 8 (by simp)
  exact pair_contra G hbest x5 x0 x7 x3 x9 x8
    h_0_7 h_3_7.symm h_3_9 h_8_9.symm h_0_8.symm
    (fun h : G.Adj x5 x0 => n_0_5 h.symm)
    (fun h : G.Adj x5 x7 => f3 x7 h_0_7 h_3_7 h)
    (fun h : G.Adj x5 x3 => triangle_of_cliqueFree' h3 h_3_4 h_4_5 h)
    (fun h : G.Adj x5 x9 => triangle_of_cliqueFree' h3 h_5_6 h_6_9 h.symm)
    (fun h : G.Adj x5 x8 => triangle_of_cliqueFree' h3 h_4_5.symm h_4_8 h.symm)
    {3, 4} (by decide) (by
      intro i hi
      fin_cases hi
      · exact ⟨x4, h_4_5.symm, h_3_4, h_4_8.symm⟩
      · exact ⟨x6, h_5_6, h_6_9.symm, h_0_6⟩)

theorem patZ_0_of
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 1)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = ({0} : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hin : ∀ j, j ∈ ({0} : Finset (Fin 5)) →
      ∃ t, G.Adj a t ∧ G.Adj (U (j - 1)) t ∧ G.Adj (U (j + 1)) t :=
    fun j hj => (mem_sSet G).1 (by rw [hS]; exact hj)
  have hout : ∀ j, j ∉ ({0} : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  obtain ⟨v0, hv0a, hv0b, hv0c⟩ := hin 0 (by decide)
  exact patZ_0 G h3 hmax hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) v0 (hU 0) (hU 1) (hU 2) (hU 3)
    (hU 4) (hn 1) (hn 2) (hn 3) (hn 4) hv0a hv0b hv0c (hout 1 (by decide)) (hout 2 (by decide))
    (hout 3 (by decide)) (hout 4 (by decide))

theorem patZ_none (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 0)
    (x0 x1 x2 x3 x4 x5 : V) (h_1_2 : G.Adj x1 x2) (h_2_3 : G.Adj x2 x3) (h_3_4 : G.Adj x3 x4)
    (h_4_5 : G.Adj x4 x5) (h_5_1 : G.Adj x5 x1) (n_0_1 : ¬ G.Adj x0 x1) (n_0_2 : ¬ G.Adj x0 x2)
    (n_0_3 : ¬ G.Adj x0 x3) (f0 : ∀ t, G.Adj x0 t → G.Adj x5 t → G.Adj x2 t → False)
    (f1 : ∀ t, G.Adj x0 t → G.Adj x1 t → G.Adj x3 t → False)
    (f2 : ∀ t, G.Adj x0 t → G.Adj x2 t → G.Adj x4 t → False)
    (f3 : ∀ t, G.Adj x0 t → G.Adj x3 t → G.Adj x5 t → False)
    (f4 : ∀ t, G.Adj x0 t → G.Adj x4 t → G.Adj x1 t → False) :
    False := by
  obtain ⟨x6, h_0_6, h_1_6⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x1 => (fun h : G.Adj x2 x0 => n_0_2 h.symm) (by rw [h]; exact h_1_2.symm))
    n_0_1
  obtain ⟨x7, h_0_7, h_2_7⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x2 => (fun h : G.Adj x1 x0 => n_0_1 h.symm) (by rw [h]; exact h_1_2))
    n_0_2
  obtain ⟨x8, h_0_8, h_3_8⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x0 = x3 => (fun h : G.Adj x2 x0 => n_0_2 h.symm) (by rw [h]; exact h_2_3))
    n_0_3
  obtain ⟨x9, h_1_9, h_8_9⟩ := exists_common_neighbor_of_maximal hmax
    (fun h : x1 = x8 => n_0_1 (by rw [h]; exact h_0_8))
    (fun h : G.Adj x1 x8 => f1 x8 h_0_8 h h_3_8)
  obtain ⟨J, hJ, x10, hx⟩ := heavy_step G h3 hδ
    (fun i => [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9].getD i x0)
    [1, 1, 1, 0, 0, 0, 0, 1, 1, 1]
    [(0, 6), (0, 7), (0, 8), (1, 2), (1, 6), (1, 9), (2, 3), (2, 7), (3, 4), (3, 8), (4, 5),
     (5, 1), (8, 9)]
    [[0, 5, 2], [0, 1, 3], [0, 2, 4], [0, 3, 5], [0, 4, 1]]
    [[1, 7, 8], [0, 2, 9]]
    (by
      simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      exact ⟨h_0_6, h_0_7, h_0_8, h_1_2, h_1_6, h_1_9, h_2_3, h_2_7, h_3_4, h_3_8, h_4_5, h_5_1,
             h_8_9⟩)
    (by
      intro F hF y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
      rcases hF with rfl | rfl | rfl | rfl | rfl
      · exact f0 y (hy 0 (by simp)) (hy 5 (by simp)) (hy 2 (by simp))
      · exact f1 y (hy 0 (by simp)) (hy 1 (by simp)) (hy 3 (by simp))
      · exact f2 y (hy 0 (by simp)) (hy 2 (by simp)) (hy 4 (by simp))
      · exact f3 y (hy 0 (by simp)) (hy 3 (by simp)) (hy 5 (by simp))
      · exact f4 y (hy 0 (by simp)) (hy 4 (by simp)) (hy 1 (by simp)))
    (by decide) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
  rcases hJ with rfl | rfl
  · have h_1_10 : G.Adj x1 x10 := hx 1 (by simp)
    have h_7_10 : G.Adj x7 x10 := hx 7 (by simp)
    have h_8_10 : G.Adj x8 x10 := hx 8 (by simp)
    exact pair_contra G hbest x3 x0 x6 x1 x10 x7
      h_0_6 h_1_6.symm h_1_10 h_7_10.symm h_0_7.symm
      (fun h : G.Adj x3 x0 => n_0_3 h.symm)
      (fun h : G.Adj x3 x6 => f1 x6 h_0_6 h_1_6 h)
      (fun h : G.Adj x3 x1 => triangle_of_cliqueFree' h3 h_1_2 h_2_3 h)
      (fun h : G.Adj x3 x10 => triangle_of_cliqueFree' h3 h_3_8 h_8_10 h.symm)
      (fun h : G.Adj x3 x7 => triangle_of_cliqueFree' h3 h_2_3.symm h_2_7 h.symm)
      {3, 4} (by decide) (by
        intro i hi
        fin_cases hi
        · exact ⟨x2, h_2_3.symm, h_1_2, h_2_7.symm⟩
        · exact ⟨x8, h_3_8, h_8_10.symm, h_0_8⟩)
  · have h_0_10 : G.Adj x0 x10 := hx 0 (by simp)
    have h_2_10 : G.Adj x2 x10 := hx 2 (by simp)
    have h_9_10 : G.Adj x9 x10 := hx 9 (by simp)
    exact pair_contra G hbest x3 x0 x6 x1 x9 x10
      h_0_6 h_1_6.symm h_1_9 h_9_10 h_0_10.symm
      (fun h : G.Adj x3 x0 => n_0_3 h.symm)
      (fun h : G.Adj x3 x6 => f1 x6 h_0_6 h_1_6 h)
      (fun h : G.Adj x3 x1 => triangle_of_cliqueFree' h3 h_1_2 h_2_3 h)
      (fun h : G.Adj x3 x9 => triangle_of_cliqueFree' h3 h_3_8 h_8_9 h.symm)
      (fun h : G.Adj x3 x10 => triangle_of_cliqueFree' h3 h_2_3.symm h_2_10 h.symm)
      {3, 4} (by decide) (by
        intro i hi
        fin_cases hi
        · exact ⟨x2, h_2_3.symm, h_1_2, h_2_10.symm⟩
        · exact ⟨x8, h_3_8, h_8_9.symm, h_0_8⟩)

theorem patZ_none_of
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ 0)
    (a : V) (U : Fin 5 → V) (hp : IsPair G a U)
    (hS : sSet G a U = (∅ : Finset (Fin 5))) :
    False := by
  obtain ⟨hU, hn⟩ := hp
  have hout : ∀ j, j ∉ (∅ : Finset (Fin 5)) →
      ∀ t, G.Adj a t → G.Adj (U (j - 1)) t → G.Adj (U (j + 1)) t → False :=
    fun j hj t h1 h2 h3 => hj (by rw [← hS]; exact (mem_sSet G).2 ⟨t, h1, h2, h3⟩)
  exact patZ_none G h3 hmax hδ hbest a (U 0) (U 1) (U 2) (U 3) (U 4) (hU 0) (hU 1) (hU 2) (hU 3)
    (hU 4) (hn 0) (hn 1) (hn 2) (hout 0 (by decide)) (hout 1 (by decide)) (hout 2 (by decide))
    (hout 3 (by decide)) (hout 4 (by decide))

end DenseTriangleFree
