# Finite box crossing duality and its exclusive dichotomy

Public module: `FK.FiniteBoxDuality` (namespace
`FK.PlaneTopology.BoxSeamBridge`). It joins the two preceding components—the
[primal/closed-bond construction](CLOSED-BOND-PRIMAL-DUALITY.md) and the
[parity-seam separation](BOX-SEAM-SEPARATION.md)—on the very same box and bond
configuration.

## Model and hypotheses

For every `ω : gridGraph.edgeSet → Bool` and natural `k`, `n`, the definition

```lean
def PrimalOpenCrossing (ω : gridGraph.edgeSet → Bool) (k n : ℕ) : Prop :=
  ∃ u v : BVert k n, u ∈ leftWall k n ∧ v ∈ rightWall k n ∧
    (primalGraph ω k n).Reachable u v
```

is open left-to-right connectivity inside the vertex box
$[0,k+1]\times[0,n]$. The closed-bond graph is the original
`closedGraph ω k n` on the existing `DVert k n`, including its two collapsed
outer vertices. The equivalence assumes `hn : 0 < n`; no probability, FK law,
infinite-volume limit or additional geometric hypothesis is used.

## The equivalence and XOR

`no_primal_crossing_of_closed_reachable` proves that a closed-bond
below-to-above path excludes an open primal left-to-right crossing. Together
with the former `exists_primal_open_walk_of_no_closed_dual`,
`primal_open_crossing_iff_no_closed_dual` proves

$$
\mathrm{PrimalOpenCrossing}(\omega,k,n)
  \iff \neg(\mathrm{closedGraph}(\omega,k,n)).
  \mathrm{Reachable}(\mathrm{inr}\,0,\mathrm{inr}\,1).
$$

`closed_reachable_xor_primal_open` is the corresponding exclusive dichotomy:
one of the two crossings exists and blocks the other. These are finite graph
statements on this bounded collapsed-dual model, not the paper's infinite
primal non-switching-order or strong-uniqueness statements.

## How the closed path is consumed

The new implication is not admitted as another geometric hypothesis:

* `chainOfPath` applies `Walk.toPath` to the closed below-to-above walk, strips
  the two outer vertices, and produces a `CellChain`. The outer-outer degree
  being zero gives path length at least two; `IsPath.getVert_injOn` excludes
  outer vertices at all interior positions and proves the cells injective.
  The first and last links prove the bottom and top row endpoints.
* `chain_closedH`, `chain_closedV`, `chain_closedBot`, and `chain_closedTop`
  identify the closed bonds crossed by every adjacency or attached to its two
  ends. The `min` form in `CellClosed` is reconciled with the `max` form in
  `bondH` and `bondV`. `chainSeam_mh_closed` and `chainSeam_mv_closed` then
  show that every nonzero bond of that exact `chainSeam` is closed.
* `openH`, `openV` are the primal open-bond indicators on the same coordinates.
  `toBox` sends integer box vertices to the `Fin (k+2) × Fin (n+1)` vertices
  used by the seam module; `boxAdj_of_primal_adj` transports every open step
  through it, preserving column/row incidence and the left/right wall indices.
* The resulting primal walk in `boxGraph (openSeam (openH ω) (openV ω))`
  contradicts `BoxSeam.closed_chain_blocks`.

The construction is noncomputable, using the ordinary witness choice for the
path's interior cells. It does not need a global embedding or a Jordan theorem,
because the completed `CellChain` supplies the sealed finite parity barrier.

## Non-vacuity and remaining limits

`allOpen_primal_crossing` and `allClosed_no_primal_crossing` check the two
opposite sides of the dichotomy on the two constant configurations.

This does **not** un-collapse the exterior dual rows or construct an infinite
un-collapsed dual graph. It supplies no cofinal exhaustion, dual
nonpercolation argument, compactness, `GlobalAtMostOne`, FK measure-theoretic
statement, or infinite primal non-switching-order conclusion. It is also not
an at-most-one-crossing-cluster theorem for a finite box: the seam module's
two-row example shows why that would be a different, generally false claim.
Theorem 1.11 therefore remains outside this result.

## Verification

The bridge was independently rebuilt against the public primal and seam
modules under Lean 4.35 with default heartbeats. All 25 exported principal
declaration audits use only `propext`, `Classical.choice` and `Quot.sound`.
There are no `sorry`, `admit`, custom axioms, `unsafe`, `native_decide`, or
heartbeat/trust overrides.
