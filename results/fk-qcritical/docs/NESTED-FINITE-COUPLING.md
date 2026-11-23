# Actual nested finite FK/FK/Bernoulli coupling

## Files

- `NestedFiniteCoupling.lean`: the construction, concrete FK instantiation, and
  conditional equation-(9) assembly.
- `NestedFiniteCouplingAudit.lean`: 24 principal axiom audits.
- `.scratch/build-one.sh`: one-target build helper using the repository Elan
  toolchain and pinned project libraries, with outputs under this member's
  `.scratch/` only.
- `check.sh`: fresh sequential rebuild, audit, and source scan.

## Proved construction

Let `GS`, `GD`, and `GO` be finite labelled multigraphs with an edge
identification

```
e : GD.Edge ⊕ GO.Edge ≃ GS.Edge.
```

`splitLaw e μΔ μO` joins a smaller configuration law and an outside law along
`e`.  Given an actual ordered pair on `GS` and one on `GD`, the construction
extends the smaller pair by sampling outside upper bits independently and
copying them into its second lower coordinate.  It then uses
`PMF.OrderedCoupling.glue` on the shared full upper configuration.

`extendPairDist_map_restrictΔ_pair` proves that restricting **both** lower and
upper coordinates of the extended pair recovers the original smaller pair
exactly.  `nestedOrderedTriple_map_snd_thd_restrictΔ_pair` proves the same for
the second/upper projection of the glued triple.

For actual finite graphs `finIndexedGraph`, `fkNestedOrderedTriple` uses
`fkUpperOrderedCoupling` for each FK coordinate.  It accepts arbitrary
boundary setoids `ξ` on `GS` and `τ` on `GD`, and uses exactly
`upperRateNN q p` for the upper Bernoulli rate.  The following are proved:

1. `fkNestedOrderedTriple_map_fst`: first marginal is the actual
   `GS.fkPMF hq hp₁.le ξ`.
2. `fkNestedOrderedTriple_map_snd_restrictΔ`: second marginal restricted by
   `restrictΔ e` is the actual `GD.fkPMF hq hp₁.le τ`.
3. `fkNestedOrderedTriple_map_thd`: third marginal is the actual full
   `GS.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)`.
4. `fkNestedOrderedTriple_ordered`: both lower coordinates are below the
   common upper coordinate on support.
5. `fkNestedOrderedTriple_outside`: the second lower coordinate agrees with
   the upper coordinate on every `GO` edge on support.
6. `fkNestedOrderedTriple_map_snd_thd_restrictΔ_pair`: the joint
   second/upper restriction is literally `fkUpperPair sD tD τ hq hp₀ hp₁`.

Thus the finite marginal/order requirements (1) and (2) of paper Lemma 2.1
are discharged in the nested setting, without a free-left/right-wired split
restriction and without pretending an FK law on `GS` restricts to an FK law on
`GD`.  The full second law is the explicitly allowed extension whose outside
marginal is independent upper Bernoulli; its outside values are copied from
the upper coordinate in the coupling itself.

## Conditional equation (9), with no `hsecond` premise

`fkNestedOrderedTriple_abs_sub_le_of_good` takes a local full event `B`, a
smaller event `A`, and a good upper event `C`, with
`B = restrictΔ e ⁻¹' A`.  Its only stochastic equality premise is equality of
the first/good and second/good intersections of the constructed triple.  The
conclusion is literally

```
|GS.fkPMF(..., ξ).real B - GD.fkPMF(..., τ).real A| ≤
  GS.bernoulliProductPMF(upperRateNN).real (restrictΔ e ⁻¹' C)ᶜ.
```

The proof converts the nested second marginal internally; the separate
`hsecond` premise of `RightWiredRestriction` is not present.

## Precise residual: not full Lemma 2.1 or Theorem 1.9

The common free-interior property on genuine maximal closed-cutset strata is
**not** asserted.  In particular, the `hgood` argument of the conditional
estimate remains to be proved for the intended nested exploration.  The joint
restriction theorems above are there to feed a smaller-pair free-interior
result without another marginal or Choquet argument.

The remaining geometric/stochastic obligations are:

1. Instantiate `e`, `A`, and `C` for the actual nested boxes, with `C` the
   genuine no-open-path event `∂Λ ↛ ∂Δ` (or its finite-maximal-cutset
   decomposition), and identify the full exceptional set and its arm event.
2. Prove that, on each actual maximal stratum in that decomposition, both
   lower interiors of this nested glued coupling have the same free FK law.
   The existing right-wired theorem is only for two FK laws on one separated
   split graph; it neither changes graph size nor enumerates the global
   maximal cutset.  It cannot simply be substituted for this obligation.
3. Transfer the resulting finite arm bound to
   `NestedArmUniqueness.eq_of_isFKLimit_of_nested_bernoulliArm_bounds`, with
   explicit roots/center/width and the subcritical-zero-percolation input.

Consequently this directory does not claim full Lemma 2.1, Lemma 1.9, strong
uniqueness, or any global DLR conclusion.

## Verification

Using Lean 4.35.0 from the repository `.scratch/elan`, independent outputs in
this member's `.scratch/oleans`, and default heartbeats:

```sh
./check.sh
```

The source and audit compile sequentially.  All 24 audit entries report only
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, `unsafe`, or
new `axiom` declaration occurs in the member-owned Lean sources.  No shared
result file or Git remote was modified.
