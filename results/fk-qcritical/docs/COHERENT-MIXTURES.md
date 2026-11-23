# Convexity and general Markov-kernel mixtures of FK DLR laws

## Deliverable

`CoherentMixtures.lean`, importing only the public `FK.ConventionEndpoints` module
(which itself publicly exposes the underlying infinite-volume interfaces).
No declarations in the shared project are changed by this deliverable.

The file proves, for the actual finite FK kernel and global configurations:

1. `map_bind`: measurable pushforward commutes with a measurable kernel
   mixture.
2. `compProd_bind`: the exterior/inner composition product distributes over
   a probability-weighted Markov-kernel mixture of its left marginal.
3. `isDLR_mixture`: if every output `outputLaw κ i` satisfies the exact DLR
   equation on a finite box, then `mixture ρ κ` satisfies that same equation.
4. `mem_dlrMeasures_mixture` and `mem_gibbsMeasures_mixture`: the same closure
   for every finite box in a fixed exhaustion, without coherence or geometric
   hypotheses beyond those already contained in the class.
5. `isDLR_convexCombination`,
   `mem_dlrMeasures_convexCombination`, and
   `mem_gibbsMeasures_convexCombination`: exact binary convexity with weights
   `t` and `1-t`.
6. `mem_gibbsMeasures_mixture_of_globalAtMostOne`: a general coherent-source
   mixture theorem on an actual countable simple graph. Different components
   may belong to different coherent geometric source conventions; each has
   almost surely at most one infinite open cluster. Every component is
   transported to the common geometric target by the accepted all-rate
   theorem, and general mixture closure assembles the result.

The mixture is an actual `Measure.bind ρ κ`, not an assertion that a mixture
exists. The binary mixture has underlying measure
`toNNReal t • μ + toNNReal (1-t) • ν`. Parameters are arbitrary `q > 0` and
`p ≤ 1`. The underlying closure results in items 1–5 use no positivity,
graph, FKG, uniqueness, or weak-limit assumption; item 6 uses precisely the
graph data, geometric conventions, and componentwise uniqueness stated there.

## Verification

Checked with the repository's existing Lean 4.35.0 toolchain using default
heartbeats:

```bash
cd results/fk-qcritical
/path/to/lean-4.35.0/lake env /path/to/lean-4.35.0/lean \
  /path/to/member/CoherentMixtures.lean
```

The command completed successfully. Its output is in `build.log`. Every new
public theorem above has a `#print axioms` audit in the source. All ten audits
contain exactly `propext`, `Classical.choice`, and `Quot.sound` (with line
wrapping only). There is no `sorry`, `admit`, `unsafe`, new axiom, extra
`set_option`, or imported draft file in this deliverable.

## Scope

This is an unconditional closure theorem for a fixed DLR specification. It
proves the convexity assertion made in the paper before Proposition 1.8, and
its general Markov-kernel strengthening. It does **not** assert the arbitrary
noncoherent weak-limit branch of Proposition 1.8(2). That separate source
comparison and its residual obligations are documented in
`SOURCE-COMPARISON.md`, not here.
