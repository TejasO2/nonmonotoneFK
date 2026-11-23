# Source comparison — Proposition 1.8(2)

This note is separate from the proof status of `CoherentMixtures.lean`.

## Primary source actually inspected

I read the primary HTML at

`.scratch/source-review/paper-v1.html`

(relative to the repository root, above `results/fk-qcritical`), using its
element text and underlying TeX annotations, not a secondary summary.
The relevant locations are:

- `S1.SS2.p8`: the source FK-limit definition. It permits an increasing
  sequence of finite subgraphs and **an arbitrary sequence of boundary
  partitions** `α_n`; it is not restricted to a coherent convention or to one
  fixed exterior configuration. The ambient graph is infinite, connected,
  and locally finite, and `0 ≤ p ≤ 1`, `q > 0`.
- `S1.SS3.p3`–`S1.SS3.p4`: a convention is a measurable compatible family of
  exterior-induced partitions satisfying the two geometric properties about
  open components and finite components. Its Gibbs class is defined by the
  DLR equations at finite subgraphs.
- `S1.SS3.p5`: the source cites Grimmett's Theorem 4.31 for the assertion
  that an FK limit with almost surely at most one infinite cluster is Gibbs
  for every convention.
- `S1.Thmproposition8`: item (2) concerns the **union** of all convention-
  Gibbs classes and the FK weak-limit class. If such a law has almost surely
  at most one infinite cluster, it belongs to every convention's Gibbs class.
- The paragraph `S1.SS3.p7` immediately before the proposition separately
  states that each `GibbsMeasures` class is convex.

## Correspondence with the existing Lean interfaces

`FK.InfiniteVolume.IsFKLimit` accurately retains arbitrary boundary setoids.
`BoundaryConvention.compatible` retains law-level nesting coherence, and
`ConventionTransport.IsGeometric` retains the two geometric properties.
`LimitOrGibbsMeasures` models the union.

For an actual countable locally finite simple graph, existing accepted
results already cover the following branches for **all** `0 ≤ p ≤ 1`:

- fixed-source coherent arbitrary-exterior weak limits:
  `EndpointGlobalFiniteEnergy.mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one`;
- weak closure of a fixed geometric DLR/Gibbs source specification:
  `EndpointGlobalFiniteEnergy.mem_dlrMeasures_of_tendsto_dlr_of_globalAtMostOne_of_le_one`;
- Gibbs-to-Gibbs convention transport:
  `ConventionTransport.mem_gibbsMeasures_of_globalAtMostOne_of_le_one`.

The endpoint weak-limit cases are unconditional in the relevant classes:
`ConventionEndpoints.mem_gibbsMeasures_zero_of_mem_limitOrGibbs` and
`..._one_of_...` use the actual all-closed/all-open endpoint laws. At interior
rates, `NoncoherentFiniteEnergy.aeAtMostOne_geometry_of_isFKLimit` derives
exterior at-most-one uniqueness from global uniqueness for an arbitrary
`IsFKLimit`, but deliberately does not claim a DLR equation.

A representation-level indexing caveat also remains: the source convention is
indexed by all finite subgraphs, while the Lean classes use a chosen genuine
`BoxExhaustion`. The present file does not prove extension from that
exhaustion to an arbitrary finite-box specification.

## Precise unresolved noncoherent interior branch

For `0 < p < 1`, an arbitrary-boundary `IsFKLimit` is not yet covered by the
coherent all-rate results. `NoncoherentStabilization.lean` makes the two
remaining inputs explicit in
`mem_dlrMeasures_of_isFKLimit_of_locallyStabilizes_of_globalAtMostOne`:

1. local DLR identities for the genuinely induced smaller-box specifications;
2. joint neighbourhood stabilization of those varying specifications against
   a geometric reference.

Neither follows merely from convergence of the scalar finite-volume laws in
the current declaration. The source alpha_n must first be converted into the
actual induced specification `π(α_n, ·)` on each fixed smaller box. After
that, one must prove enough analytic convergence for weak reconstruction.
Dense-probe diagonalization is expressly insufficient for the second point.
More generally, pointwise convergence plus local constancy does not imply
`LocallyStabilizes`; even an ultrafilter limit can leave the joint uniformity
and measurability issues unresolved. Finite energy gives the exterior
uniqueness geometry but does not itself supply these two inputs.

Accordingly, this submission makes **no** unrestricted
`IsFKLimit + GlobalAtMostOne => DLR` declaration and does not use the finite
one-edge counterexample. Neither the source's infinite connected locally
finite statement nor the existing scoped noncoherent theorem is claimed to be
refuted.

## What the new Lean file contributes

`CoherentMixtures.lean` proves the source's separate convexity assertion in a
stronger form: closure under arbitrary probability-weighted Markov-kernel
mixtures, together with binary convexity for both DLR and coherent Gibbs
classes. In addition, `mem_gibbsMeasures_mixture_of_globalAtMostOne` directly
extends the coherent-Gibbs branch of Proposition 1.8(2) to a genuinely indexed
mixture whose components may use **different** coherent source conventions.
Each component's at-most-one hypothesis is used separately; no uniqueness is
asserted for the entire mixture without these component hypotheses.

These results are fully proved and axiom-audited. They are not offered as a
proof of the noncoherent weak-limit branch above.
