/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import JinLib.Heavy

/-!
# Vertices missing a 5-cycle

A *pair* `(a, U)` consists of a closed walk `U` of length 5 and a vertex `a` adjacent to no vertex
of `U`. For such a pair, `sSet G a U` is the set of indices `i` such that some neighbour of `a` is
adjacent to both `U (i - 1)` and `U (i + 1)`; if it is all of `Fin 5`, the pair spans a homomorphic
image of the Grötzsch graph. The proof of the key lemma chooses a pair maximising `|sSet G a U|`;
`pair_contra` exhibits a pair with a larger set, contradicting this choice.
-/

@[expose] public section

namespace DenseTriangleFree

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `U` is a closed walk of length 5 and `a` is adjacent to none of its vertices. -/
def IsPair (a : V) (U : Fin 5 → V) : Prop :=
  (∀ i, G.Adj (U i) (U (i + 1))) ∧ ∀ i, ¬ G.Adj a (U i)

open Classical in
/-- Indices `i` such that a neighbour of `a` sees both `U (i - 1)` and `U (i + 1)`. -/
noncomputable def sSet (a : V) (U : Fin 5 → V) : Finset (Fin 5) :=
  Finset.univ.filter fun i => ∃ t, G.Adj a t ∧ G.Adj (U (i - 1)) t ∧ G.Adj (U (i + 1)) t

theorem mem_sSet {a : V} {U : Fin 5 → V} {i : Fin 5} :
    i ∈ sSet G a U ↔ ∃ t, G.Adj a t ∧ G.Adj (U (i - 1)) t ∧ G.Adj (U (i + 1)) t := by
  classical
  simp [sSet]

/-- A pair with more than `m` witnessed indices contradicts the maximality of `m`. -/
theorem pair_contra {m : ℕ}
    (hbest : ∀ (b : V) (W : Fin 5 → V), IsPair G b W → (sSet G b W).card ≤ m)
    (b w0 w1 w2 w3 w4 : V) (e0 : G.Adj w0 w1) (e1 : G.Adj w1 w2) (e2 : G.Adj w2 w3)
    (e3 : G.Adj w3 w4) (e4 : G.Adj w4 w0)
    (n0 : ¬ G.Adj b w0) (n1 : ¬ G.Adj b w1) (n2 : ¬ G.Adj b w2) (n3 : ¬ G.Adj b w3)
    (n4 : ¬ G.Adj b w4) (Q : Finset (Fin 5)) (hQ : m < Q.card)
    (hw : ∀ i ∈ Q, ∃ t, G.Adj b t ∧ G.Adj (![w0, w1, w2, w3, w4] (i - 1)) t ∧
      G.Adj (![w0, w1, w2, w3, w4] (i + 1)) t) : False := by
  have hp : IsPair G b ![w0, w1, w2, w3, w4] := by
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> assumption
  have h1 := hbest _ _ hp
  have h2 : Q ⊆ sSet G b ![w0, w1, w2, w3, w4] := fun i hi => (mem_sSet G).2 (hw i hi)
  have := Finset.card_le_card h2
  omega

end DenseTriangleFree
