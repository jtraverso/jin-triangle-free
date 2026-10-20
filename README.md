# Jin's theorem on dense triangle-free graphs in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

All statements are in the namespace `JinTheorem`:

1. `jin`, **Jin's theorem (1995)**. A finite triangle-free graph (`G.CliqueFree 3`) on `n`
   vertices with minimum degree `δ(G) > 10n/29` (stated as `10 n < 29 δ(G)`) is 3-colourable.
2. `jin_sharp`, **sharpness (Häggkvist 1982)**. For every `m ≥ 1` there is a triangle-free
   `10m`-regular graph on `29m` vertices that is not 3-colourable: the blow-up of the Grötzsch graph
   with weights `3m` on the outer 5-cycle, `2m` on the five inner vertices and `4m` on the centre.

This extends the case `r = 2` of the Andrásfai–Erdős–Sós theorem (`δ > 2n/5` forces
bipartiteness), which is in Mathlib as `SimpleGraph.colorable_of_cliqueFree_lt_minDegree`. The
statements use only Mathlib's definitions. Mathlib does not have Jin's theorem.

## Files

- [`Challenge.lean`](Challenge.lean): the audited statements. It imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`JinLib/`](JinLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Reduction to maximal graphs** (`Maximal.lean`). Adding edges keeps the graph triangle-free and
  does not decrease the minimum degree, so it suffices to colour maximal triangle-free graphs, in
  which any two distinct non-adjacent vertices have a common neighbour.
* **The Grötzsch obstruction** (`Grotzsch.lean`). With weights `3, 2, 4` (total 29) on the outer
  cycle, inner vertices and centre of the Grötzsch graph, every independent set has weight at most
  10. So if a triangle-free `G` receives a homomorphism from the Grötzsch graph, then
  `29 δ(G) ≤ 10 n`. The Grötzsch graph is not 3-colourable (checked by `decide +kernel`).
* **Key lemma** (`KeyLemma.lean`, `Patterns.lean`, `Heavy.lean`). In a maximal triangle-free graph
  with `29 δ > 10 n`, every vertex is adjacent to some vertex of every closed walk of length 5. An
  extremal counterexample is reduced, by the symmetries of the 5-cycle, to eight patterns, each
  refuted by maximality, by a weighted pigeonhole step (where `29 δ > 10 n` is used) or by
  extremality; the last pattern is a homomorphic image of the Grötzsch graph.
* **Colouring** (`Bipartite.lean`). For any vertex `a`, no odd closed walk avoids the neighbourhood
  of `a` (strong induction on the length, using the key lemma for length 5), so the
  non-neighbourhood of `a` is bipartite; the neighbourhood of `a` is independent and gets the third
  colour.
* **Sharpness** (`Blowup.lean`). The weighted blow-up of the Grötzsch graph is triangle-free and
  `10m`-regular, and a 3-colouring of it would restrict to one of the Grötzsch graph.

## Sources

* G. P. Jin, *Triangle-free four-chromatic graphs*, Discrete Math. 145 (1995) 151–170,
  doi:10.1016/0012-365X(94)00063-O.
* R. Häggkvist, *Odd cycles of specified length in non-bipartite graphs*, in: Graph Theory
  (Cambridge, 1981), North-Holland Math. Stud. 62 (1982) 89–99, doi:10.1016/S0304-0208(08)73552-7.
* C. C. Chen, G. P. Jin, K. M. Koh, *Triangle-free graphs with large degree*, Combin. Probab.
  Comput. 6 (1997) 381–396, doi:10.1017/S0963548397003167.
* B. Andrásfai, P. Erdős, V. T. Sós, *On the connection between chromatic number, maximal clique
  and minimal degree of a graph*, Discrete Math. 8 (1974) 205–218,
  doi:10.1016/0012-365X(74)90133-2.

## Authorship and use of AI

The author chose the result. The statements and proof plans were written with Claude in Claude
Code (the extremal example and the weight bound were first checked numerically). Harmonic's
Aristotle produced the proofs in two runs (the first proved the sharpness, the weight lemma and
the reduction to maximal graphs; the second found the key lemma on closed walks of length 5 and
completed the proof), which were audited and rebuilt locally. Lean checks everything
mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
