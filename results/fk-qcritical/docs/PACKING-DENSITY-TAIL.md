# Positive-density bounded-range AG device packings and activation tails

Direction 4 of swarm `smwttt0li` (member `m2`).  All declarations below are
compiled against the pinned project toolchain (Lean 4.35.0, project `FK`
imports, default heartbeats) and audited: every one depends only on
`propext`, `Classical.choice`, `Quot.sound`.

Files (all in this directory, not in the shared tree):

* `AGPackingDensity.lean` — the abstract covering/density theorem, the exact
  activation-cylinder law and tail, and two reusable graph-metric bricks.
* `AGPackingDensityExample.lean` — a concrete non-vacuous instance.
* `AGPackedSleeveDensity.lean` — the density theorem applied to the repository's
  actual uniform whole-template sleeve packing.

## 1. What is proved

### 1.1 Covering counts give positive density

`FK.AGPackingDensity.EdgeMetric` bundles an edge metric `dist` with finite balls
and their characterisation `g ∈ ball f n ↔ dist f g ≤ n`, symmetry and the
triangle inequality.  `lineMetric` constructs it for the line graph of any
connected locally finite graph.

* `card_ball_le_mul_card_devices`: if the pivots of the devices indexed by a
  finite set `J` `K`-cover the edge set and every radius-`K` ball around a pivot
  has at most `D` edges, then `|ball f n| ≤ D * |J|`.
* `linear_growth_le_mul_card_devices`: with the growth input
  `n + 1 ≤ |ball f n|` this becomes `n + 1 ≤ D * |J|`, i.e. at least `(n+1)/D`
  devices.
* `density_ncard`: the form that applies to an *infinite* device index set
  (the actual packing `M : Set (H ≃g H)`):
  `n + 1 ≤ D * (Set.ncard {i | dist f (p i) ≤ n + K}).`  Finite index sets,
  countability, and finiteness of the packing are not assumed; finiteness of the
  counted device set follows from injectivity of the pivot map into a finite
  ball.
* `card_le_card_ball`: the matching upper bound — pairwise-disjoint devices have
  distinct pivots, so a radius-`n` ball meets at most `|ball f n|` devices.
  Density is sandwiched between `1/D` and `1`.
* `exists_far_edge`: no finite device set `K`-covers an edge metric with linear
  growth.  Qualitative form of the same statement.

Note carefully: disjointness of templates is *not* used in the covering count; it
is used only through injectivity of the pivot map, and on the sleeve packing that
injectivity is `pivot_injOn_of_uniform_packing`.

### 1.2 Exact activation cylinder and tail

`allClosed J` is the cylinder where every coordinate of `J` is inactive.

* `bernoulliProduct_allClosed`: for the actual infinite product Bernoulli law
  `FK.Configuration.bernoulliProduct r`, the all-inactive cylinder has the exact
  probability `∏_{e∈J} ofReal (1 - r e)`.
* `bernoulliProduct_allClosed_toReal_le`: if every rate is at least `s`, the
  probability is at most `(1 - s)^{|J|}`.
* `exists_card_ge`, `exists_allClosed_le`: if the ball device sets satisfy the
  density inequality `n + 1 ≤ D * |J n|` with `D > 0`, then for every activation
  rate `s > 0` and every `ε > 0` some ball has all-inactive probability below
  `ε`.  The input is only the explicit bound `(1 - s)^{|J n|}`; no limit of a
  probability is formed by exchanging a derivative or an infinite sum.

### 1.3 The actual uniform sleeve packing

`packed_sleeves_density` (namespace `FK.AGPackingDensity.PackedSleeve`) works on
`graph H` with `H` connected, locally finite, `[DecidableEq V]`, a nonempty
finite base-bond set `S`, `e₀ ∈ S`, and the pairwise-disjoint translated-template
packing `M` (`translateSupport (automorphism H φ) (template H S)`).  Its
conclusion is

```
n + 1 ≤ D * Set.ncard {φ : M | dist f (pivot φ) ≤ n + K}
```

with the line-graph metric of `graph H`, where `pivot φ` is the transported base
bond of `φ`.  Injectivity of the pivot map is *derived* from pairwise
disjointness via `pivot_injOn_of_uniform_packing`; the three numeric inputs
`hcover` (bounded-distance covering), `hD` (radius-`K` ball bound) and `hlin`
(linear growth) are explicit hypotheses.  `cover_of_boundedDistance` identifies
`hcover` with the pointwise `BoundedDistance` form produced by
`exists_uniform_sleeve_packing`.

### 1.4 A concrete non-vacuous instance

`AGPackingDensityExample` works on the integer line `ℤ` with bonds `{n, n+1}`:

* `bond_essential`: *every* bond is an Aizenman–Grimmett essential device
  (`OnDoubleRay → Essential`, from `FK.EssentialEnhancement`).  The line is
  connected, locally finite and of degree two.
* `cover_thirds`: the three-periodic pivots `3k` are within distance one of every
  integer.
* `density_lower`: every finite pivot set that covers the line satisfies
  `n + 1 ≤ 3 * |J|` for all `n`; `density_pivots` is the infinite-family
  `Set.ncard` form around an arbitrary centre; `density_upper` is the matching
  upper bound.
* `activation_tail_le`, `activation_tail_eventually`: the radius-`n` window
  (`2n+1` devices) has all-inactive probability at most `(1 - s)^{2n+1}`, which
  is arbitrarily small at every `s > 0`.

So the density-and-tail package is instantiated on a genuine connected locally
finite bounded-degree graph with genuine essential devices, at density `1/3`.

### 1.5 Reusable graph-metric bricks

* `finite_dist_ball`: distance balls of a connected locally finite graph are
  finite (explicit induction with a shortest-walk prefix).
* `finite_edges_through`, `lineGraph_locallyFinite`: the line graph of a locally
  finite graph is locally finite (via `incidenceSet`).
* `lineMetric`: the resulting `EdgeMetric` on the line graph.

## 2. Exact residual

The only step not carried out is deriving the three numeric inputs for
`graph H` from a degree hypothesis on `H`:

1. `hD`: a uniform bound on the number of edges of `graph H` in a line-graph ball
   of radius `K`.  This follows from a uniform vertex-degree bound on `H`
   (`|ball_K| ≤ 2K * (Δ + 1) * something`), which is not formalised here.
2. `hlin`: linear line-graph growth of `graph H` (`n + 1 ≤ |ball f n|`), which
   follows from an infinite ray in `graph H`.
3. `hcover`: the bounded-distance covering of `graph H` by the selected pivots,
   which on the packing produced by `exists_uniform_sleeve_packing` is exactly
   its `BoundedDistance` component (the packing theorem is stated with the
   covering property, not with the ball bound).

With those three inputs — all of them concrete finite or geometric facts, none of
them an assumed `hAG`, a reference law, or a critical parameter — the density
statement becomes unconditional on a bounded-degree quasi-transitive base.

## 3. What is *not* claimed

* No critical parameter, no reference curve strictness, no strict critical shift
  and no `hAG`.  In particular nothing here duplicates the strict-shift
  assertions of Aizenman–Grimmett; the density constant produced is a *lower*
  bound on device counts, not a positive speed.
* No claim about the FK DLR specification, Theorem 1.4, 1.9, 1.10 or 1.11.
* The concrete instance is the integer line, not a general graph; it exists to
  exhibit the constants and to certify that the hypotheses are satisfiable.
* Template disjointness alone gives `edgeUnique`; the counting theorem uses it
  only for pivot injectivity, and the tail is stated for the actual independent
  product law, not a finite-volume surrogate.

## 4. Verification

```
TC=/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0
R=/workspace/nucleus/work/projects/p-a57b611ad60a4cbc99162d56e011665d/repo/results/fk-qcritical
PK=$R/.lake/packages
export LEAN_PATH="$PWD:$TC/lib/lean:$PK/Cli/.lake/build/lib/lean:$PK/batteries/.lake/build/lib/lean:$PK/Qq/.lake/build/lib/lean:$PK/aesop/.lake/build/lib/lean:$PK/proofwidgets/.lake/build/lib/lean:$PK/importGraph/.lake/build/lib/lean:$PK/LeanSearchClient/.lake/build/lib/lean:$PK/plausible/.lake/build/lib/lean:$PK/mathlib/.lake/build/lib/lean:$R/.lake/build/lib/lean"
$TC/bin/lean -o AGPackingDensity.olean AGPackingDensity.lean
$TC/bin/lean -o AGPackingDensityExample.olean AGPackingDensityExample.lean
$TC/bin/lean -o AGPackedSleeveDensity.olean AGPackedSleeveDensity.lean
$TC/bin/lean Audit.lean
```

`Audit.lean` contains the twenty-one exact `#print axioms` lines; the recorded
output is `audit-output.txt`.  There is
no `sorry`, `admit`, custom axiom or `unsafe` declaration in any of the three
files.

## Release integration

The public modules preserve the independently checked proofs and change only
worker-local imports to `FK.AGPackingDensity`. The generic tail is independent
of the metric covering theorem; the latter supplies growing device sets.
`hD`, `hcover`, and `hlin` remain explicit in the packed-sleeve adapter, and
`density_lower` on $\mathbb Z$ is a bound for an arbitrary covering family,
not merely the selected three-periodic one. No unproved degree-bound derivation
is included in this release.
