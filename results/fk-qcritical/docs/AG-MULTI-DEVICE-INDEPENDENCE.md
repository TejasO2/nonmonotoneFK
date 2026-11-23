# Multi-device independent sleeve activations

## Files

- `AGMultiDeviceIndependence.lean`: complete member-local source, importing only public `FK.*` modules. It leaves the existing single-shared-activation source unchanged.
- `Audit.lean` and `audit-output.txt`: exact axiom audits of 19 principal declarations.
- `AGMultiDeviceIndependence.olean`: member-local Lean 4.35 build used by the audit.

## Proved content

For `S : ι → Finset H.edgeSet`, `independentSupport H S` gives device `i` the sleeve edges of `S i`. Configurations have type `(graph H).edgeSet ⊕ ι → Bool`, so different devices have genuinely different activation coordinates.

The geometry proofs construct the same actual two-edge replacement walks as the single sleeve, but force `Sum.inr i`. Consequently a selected bond pivot becomes an activation pivot of device `i`. Both the open-connection and actual one-arm event are covered. The normalized finite-product estimate is first proved per bond and per device and then summed. If every `(S i).card = R` and `μ` is the actual `FinProb.pi` joint law, the total estimate is

```
δ^R * Σ_i Σ_{e ∈ S i} μ(EdgePivotal A (baseEdge H e))
  ≤ (2^R * R) * Σ_i μ(ActivationPivotal A i).
```

`pi_map_jointSplit`, `pi_map_activations`, `activationProfile_marginal_mass`, and `activationEvent_marginal` prove exact factorization and summing-out of ordinary bonds. In particular, the probability of a complete prescribed activation profile is the product of its per-device coordinate masses.

For the comparison line, every activation coordinate independently has velocity `1`, and every selected ordinary bond has velocity `-c`. Under pairwise-disjoint annuli, the derivative is exactly

```
-c * Σ_i Σ_{e ∈ S i} PivotalProbability(baseEdge H e)
  + Σ_i PivotalProbability(activation i).
```

With `R > 0`, all `(S i).card = R`, and `δ = min a (1-b)`, the normalized speed is

```
c = δ^R / (2^R * R).
```

The source proves nonnegativity of the displayed derivative on the interior box, monotonicity on the endpoint-safe interval, and the endpoint comparison both for `eventWeight` and for the actual normalized independent product laws. There is no multiplicity collapse to one shared activation.

The disjointness premise is supplied by the existing whole-template packing via `disjoint_packedIndependentAnnuli_fintype`. Additional exact packing consequences are:

- ordinary moved-base support has cardinality `F.card * S.card`;
- activation-edge union cardinality equals the sum of the individual support cardinalities and is at most `F.card * (2 * S.card)`;
- an edge belongs to at most one selected activation support;
- the existing whole-template size bound remains separate and unchanged.

## Validation

Elaborated with the already installed `leanprover/lean4:v4.35.0` toolchain and the public project's `.lake` environment, at default heartbeats. The placeholder/option scan is empty. Every declaration in `Audit.lean` has exactly the axiom dependencies:

```
[propext, Classical.choice, Quot.sound]
```

## Explicit residuals

This is a finite-window, finite-device result. It assumes finite joint coordinate types for probabilities and derivatives, a common positive annulus size for the displayed common speed, and pairwise-disjoint annuli for derivative reindexing (discharged by the packed-family lemmas). It does not construct an infinite-volume reference law, interchange a limit, prove an AG critical shift, or discharge any `hAG`/whole-paper hypothesis.
