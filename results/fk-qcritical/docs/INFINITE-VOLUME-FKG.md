# Positive association for arbitrary FK weak limits

Public module: `FK.InfiniteVolumeFKG` (namespace
`FK.InfiniteVolume.InfiniteVolumeFKG`). This lifts the finite FKG bridge to an
arbitrary FK weak limit with arbitrary boundary-setoid schedule.

For $q \ge 1$ and $0\le p\le1$, `mul_le_inter_of_isFKLimit` proves that every
measurable increasing pair satisfies

$$\mu(A)\,\mu(B)\le\mu(A\cap B).$$

No coherence condition, one-cluster condition or extra DLR requirement is part
of the statement. `mul_le_inter_of_mem_fkLimitMeasures` forgets the particular
schedule. `apply_mul_le_apply_inter_of_isFKLimit` and
`inter_le_mul_of_isFKLimit` give the corresponding `ProbabilityMeasure`
application and increasing/decreasing forms.

## Why arbitrary increasing measurable events work

1. **Finite volume.** `fkMeasure_mul_le_inter` applies the actual normalized
   finite FKG inequality to indicator observables. Both endpoint laws are
   separately handled as Dirac laws, so the main double-event inequality still
   holds at the endpoints. `fkMeasure_mono_p_of_lt_one` gives parameter
   monotonicity for increasing events, scoped $p_1\le p_2<1$.
2. **Box laws.** The interior restriction of an increasing global event is
   increasing. `finiteVolumeLaw_mul_le_inter` relates its finite-box and
   finite-graph masses. `finiteVolumeLaw_mono_p` transports the rate bound.
3. **Cylinder limits.** A clopen event supported on a finite coordinate set
   has continuous mass along weak convergence. There is an eventual box
   support for every finite cylinder, so
   `cylinder_mul_le_inter_of_isFKLimit` passes the two-event inequality to a
   supplied actual `IsFKLimit`. A common schedule also gives
   `stochasticallyDominates_of_isFKLimit_p` for $p_1\le p_2<1$.
4. **All increasing measurable events.** `restrictionNeighborhood` gives a
   decreasing cylinder approximation of a compact increasing set. The measure
   of that decreasing sequence converges to the compact set's measure, yielding
   `mul_le_inter_of_isCompact_upper`. Inner regularity and the minimal
   increasing `upperClosure` extend the result first to one compact/one
   measurable increase, then to both directions. This is an actual
   product-topology and measure approximation proof, not a re-labelling of
   finite equal-cylinder uniqueness.

`mul_le_inter_of_tendsto_of_cylinder` packages the abstract transfer for any
weakly convergent sequence satisfying positive association on all supported
increasing events. `bernoulliConst_mul_le_inter` gives a non-vacuous
$q=1$ instance via an already constructed FK weak limit.

## Deliberate limits

The module does not build an FK limit or the canonical free/wired limits and
does not infer DLR membership, Prop. 1.8(2), Theorem 1.4/1.9/1.10/1.11, or a
critical shift. There is no uniqueness implication, no Burton–Keane or
at-most-one-cluster result, and no $q<1$ positive-association claim. The full
FKG inequality for arbitrary random variables is not supplied, only its event
indicator form. Parameter monotonicity is scoped to $p_1\le p_2<1$; $p_2=1$ is
not claimed from that wrapper.

The exact source was independently rebuilt with pinned Lean 4.35/default
heartbeats. All 19 principal export audits report only the standard
foundational axioms and there are no proof placeholders or trust overrides.
