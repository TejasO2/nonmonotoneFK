# Radial-root obstruction and root-attached repair criterion

## Compiling deliverable

`NestedRadialCounterexample.lean` imports only public `FK.*` modules and Mathlib.
It contains no `sorry`, `admit`, `unsafe`, new axioms, or heartbeat overrides.
Checked with Lean 4.35.0 using:

```sh
cd results/fk-qcritical
PATH=/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH \
  lake env lean ../../.ultramath/smwsz39k5/m2/NestedRadialCounterexample.lean
```

(The exact relative path from the repository root is
`../../.ultramath/smwsz39k5/m2/NestedRadialCounterexample.lean`.)
All eight printed axiom audits report exactly `propext`, `Classical.choice`, and
`Quot.sound`.

## Exact scoped results

The connected locally finite graph `lineGraph` is the Hasse graph on `ℕ`.
`lineGraph_dist_zero` proves its distance formula from explicit walks and a
walk-length lower bound.

For `p < 1`, `ae_nonPercolating_percolation_line` proves that homogeneous
Bernoulli percolation on this graph is almost surely nonpercolating.  An open
cluster rooted at `o` and extending arbitrarily far forces every edge to its
right to be open (`rootInfinite_subset_tailAllOpen`).  A closed-edge cut proves
that implication, and `tailAllOpen_le_pow` gives the exact finite-cylinder upper
bound `p^N`, whose limit is zero.

Independently, `lineEdge_open_subset_radialFarConnection` proves the exact
inclusion

```text
{ω | ω (lineEdge R)} ⊆
  farConnection lineGraph (innerBall lineGraph_connected 0 (R+1)) 0 (R+1).
```

Thus `radialFarConnection_real_lower` gives real mass at least `p` at every
positive radius.  The main obstruction,
`radial_nonvanishing_of_nonPercolating`, combines, for every `0 < p < 1`:

* almost-sure nonpercolation; and
* non-convergence to zero of the actual same-radius whole-ball
  `farConnection` sequence used on the right-hand side of
  `NestedMetricRegionSplit.cylinder_abs_sub_le_radial_farConnection_of_good`.

This refutes only the proposed deduction "nonpercolation implies that this
whole-ball/same-radius error vanishes".  It does **not** refute fixed-root arm
vanishing, the source theorem, or Theorem 1.9, and it does not assert a positive
lower bound for the nested cylinder difference or for the bad stratum itself.

The positive repair criterion is
`RootAttached.mem_finiteRootArms_of_not_mem_maximalSplitStratum`.  If roots lie
in the fixed ball of radius `L`, right vertices lie beyond radius `n+L`, and
**every left vertex is openly connected to some root in the same
configuration**, then failure of the maximal split implies
`finiteRootArms G roots n`.  The proof extends the existing left/right path by
the root attachment and applies the graph-distance triangle inequality.
`RootAttached.bad_maximalSplit_subset_closedLocalEvent_finiteRootArms` transports
this criterion to the actual canonical nested split and `closedLocalEvent`.
Consequently the existing theorem
`tendsto_measureReal_finiteRootArms_of_ae_nonPercolating` applies to this error
under nonpercolation, without any growing root set.

## Residual mathematical work

The radial ball/complement split does not supply the displayed root-attachment
premise; its left vertices are all vertices of the growing ball.  A complete
refinement must construct or select an exploration stratum satisfying that
premise (or an equivalent extension property), prove the corresponding `hgood`,
and supply the finite-coordinate realization needed by the nested assembly.
Those steps are not claimed here.

No paper-source comparison was needed for this implementation-level scoped
counterexample.  The result concerns the explicitly documented Lean radial
wrapper and is not a source-theorem counterexample.
