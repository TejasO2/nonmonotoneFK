# Stage 10, member m2: nested restriction and subcritical assembly

## Scope

This is a genuine partial step in direction (C), not full Lemma 2.1 and not the
whole Theorem 1.9.  The source checked was Section 2 of
[arXiv:2512.16486](https://arxiv.org/html/2512.16486), especially the statement
of Lemma 2.1, equation (9), and the two nested limits following it.

Two gaps were addressed independently.

### 1. `RightWiredRestriction.lean`

The public `equation_nine_rightWired` compares two laws on the same transported
configuration type.  Lemma 2.1 instead prescribes the second marginal only
after restriction to `E_Δ`.

* `equation_nine_rightWired_second_restrict` transports the public estimate to
  an arbitrary restricted second measure.  It assumes a measurable restriction
  `restrictΔ`, a measurable local readout `readΛ`, factorization of the actual
  split-interior observation through these maps, and the explicit pushforward
  identity `hsecond`.
* `equation_nine_rightWired_second_fkRestriction` specializes the target to the
  actual finite `B.fkMeasure hq hp₁.le α`, with an arbitrary boundary setoid
  `α`.  Again `hsecond` explicitly identifies that measure with the restriction
  of the second right-wired coordinate.

These results do **not** construct that pushforward identity for arbitrary
nested boxes, and do not enlarge the free-left/right-supported split-graph
class to arbitrary left or cross wiring.

### 2. `NestedArmUniqueness.lean`

The following are proved for the actual vendored open-walk graph model.

* `tendsto_measureReal_armEvent_of_ae_nonPercolating`: one-arm real
  probabilities tend to zero by continuity from above and almost-sure
  nonpercolation.
* `tendsto_measureReal_finiteRootArms_of_ae_nonPercolating`: the same holds for
  a union over a `Finset` of roots.  No uncountable intersection of null sets
  is used.
* `farConnection_add_subset_finiteRootArms`: if every root has distance at most
  `L` from `o`, an actual open connection from that root set to distance
  `n + L` from `o` contains an `n`-arm from one of the roots.  The proof uses
  the graph-distance triangle inequality.
* `measurableSet_farConnection`, `farConnection_add_antitone`, and
  `tendsto_measureReal_farConnection_add_of_ae_nonPercolating` supply the
  corresponding measurable, nested-event, and vanishing-probability interface.
* `ae_nonPercolating_percolation_of_percolationProb_eq_zero`: actual Bernoulli
  percolation is almost-surely nonpercolating when `percolationProb G o p' = 0`
  at every root.  Countability of the vertex type makes the simultaneous
  null-set step legitimate.
* `probabilityMeasure_eq_of_nested_finiteRootArm_bounds` and
  `eq_of_isFKLimit_of_nested_finiteRootArm_bounds`: two weakly convergent
  sequences, and then two genuine `IsFKLimit` approximations along possibly
  different box exhaustions and boundary sequences, have the same limit if
  their eventual nested absolute differences are bounded by the finite-root
  arm error.  The proof uses weak convergence on real cylinder probabilities,
  the existing nested-limits lemma, and equality on all finite-base cylinders.
* `eq_of_isFKLimit_of_nested_bernoulliArm_bounds` specializes the upper law to
  actual independent bond percolation and takes the error to be a genuine
  `farConnection` metric-boundary event.  Its `hzero`, `hwidth`, and `hbound`
  hypotheses are visible in the declaration.

## Precise remaining obligations

The following work is still required before claiming full Lemma 2.1 or
Theorem 1.9. The later [nested finite-coupling module](NESTED-FINITE-COUPLING.md)
now supplies the first/third marginals and the exact second restriction; its
second-marginal conversion is internal, so a separate `hsecond` premise is no
longer needed for that constructed triple.

1. Instantiate the constructed triple on the actual `Λ ⊆ Δ ⊆ Σ` geometry and
   identify its observation and good/no-connection events.
2. Establish `hgood`: the common free-interior law on the genuine global maximal
   closed-cutset strata, including arbitrary intended nested-box boundaries.
   The older one-split-graph right-wired theorem does not discharge this.
3. Identify the full exceptional set with the intended `∂Λ ↔ ∂Δ` event or an
   exact finite-maximal-cutset decomposition, including its all-closed support.
4. Instantiate `roots`, `center`, `width`, and `hwidth` for the chosen nested
   box geometry so that the finite estimate has the required form.

Only after these inputs does the weak-limit assembly yield uniqueness.

## Verification

All files are in this member directory.  No shared results file or Git remote
was changed.  Compilation used the repository Elan at `.scratch/elan`, Lean
4.35.0, the project's pinned `LEAN_PATH`, and default heartbeats.  Both source
modules compiled independently, and `.olean` outputs were written under this
member's `.scratch/oleans`.

`NestedAssemblyAudit.lean` imports those outputs and audits 13 principal
declarations.  Every audit reports only
`[propext, Classical.choice, Quot.sound]`; the complete output is in
`.scratch/logs/NestedAssemblyAudit.log`.  A source scan found no
`sorry`/`admit`/`unsafe`/new `axiom` declarations.
