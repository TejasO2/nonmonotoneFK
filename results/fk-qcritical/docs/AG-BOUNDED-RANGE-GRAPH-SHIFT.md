# Bounded-range strict shift on a logarithmic bundle graph

## Actual graph and activation model

`BoundedRangeGraphShift.lean` constructs the simple graph on
`ℕ ⊕ Σ n, Fin (width n)`, with `width n = Nat.log 2 (n+1)+1`. Route `r` in
bundle `n` joins backbone vertex `n` to its internal vertex by a random route
edge and that internal vertex to backbone vertex `n+1` by a deterministically
open stem. `bundleGraph_connected` proves connectedness and
`bundleGraphLocallyFinite` proves local finiteness of the resulting graph;
width grows only with the bundle index, so each particular vertex has finite
degree.

Every random route edge has an independent bond bit at rate $p$ and an
independent activation bit at rate $s$. Its enhanced state is the Boolean OR;
no activation touches another edge. `pairedRouteLaw_map_routeOr` and
`jointRouteLaw_map_routeOr` prove the exact normalized marginal at rate
`orUnit p s`, with real value $p+(1-p)s$. This is genuine one-edge-range local
activation, not a synchronized global activation. The full graph law is
nevertheless **inhomogeneous** because the stems are deterministically open.
The example is not claimed to be quasi-transitive or bounded-degree.

## Exact percolation event

`graphConfig_preimage_rootPercolates` identifies the preimage of actual infinite
root-cluster percolation with `AllCrossed`: root percolation happens exactly
when every bundle has an open random route edge. Crossing all bundles connects
infinitely many backbone vertices. Conversely, if bundle $N$ is entirely closed,
the open root cluster is contained in an explicitly finite collection of earlier
route and backbone vertices.

Bundle $n$ has failure probability
$(1-p)^{\mathrm{width}(n)}$. Cauchy condensation gives summability when
$p>1/2$ and nonsummability when $p\le1/2$. Independent bundle failures and
second Borel--Cantelli give zero probability of `AllCrossed` in the latter case.
In the former case, the exact product probabilities of finite prefix events
pass through their decreasing intersection, and nonvanishing of the infinite
product gives positive probability. These steps do not exchange derivatives
with an infinite-volume limit.

## Exact critical parameters and scope

`baseCritical_eq_half` proves $p_c=1/2$ for the actual resulting graph law.
At fixed activation rate $1/4$, the effective rate is $p+(1-p)/4$, and
`enhancedCritical_quarter_eq_third` proves the exact enhanced threshold $1/3$.
`strict_critical_shift_quarter` concludes $1/3<1/2$ between the explicitly defined
critical parameters. They use the same `sSup` zero-probability convention as the
project's other critical-point constructions.

This is a complete bounded-range strict critical shift **for this constructed
inhomogeneous graph and activations**, not a holomorphic/discontinuity argument
and not the general Aizenman–Grimmett reference theorem. It does not discharge
`hAG`, construct an essential-enhancement window on a quasi-transitive
bounded-degree graph, or complete Theorem 1.4, 1.9, 1.10, or 1.11.

## Verification

The exact candidate was independently rebuilt with pinned Lean 4.35.0 and
default heartbeats. Its fourteen principal declarations were independently
audited with the repository's axiom checker: only `propext`, `Classical.choice`,
and `Quot.sound` occur. No placeholders, custom axioms, unsafe declarations, or
elaboration overrides are present. The release check also builds the public
import and repeats all principal audits.
