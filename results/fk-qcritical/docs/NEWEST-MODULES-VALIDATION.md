# Direction H: validation and compiling interfaces

## Outcome

The three newest public modules were checked against their declarations and
against Beffara--Faipeur--Oke, *A new bound for the critical point of the FK
model for q<1*, [arXiv:2512.16486v1](https://arxiv.org/abs/2512.16486v1).
No new false theorem or undocumented representational restriction was found.
Their documented scope restrictions remain essential. The new compiling source
is `NewestModulesValidation.lean`; it adds DLR-measurability/support interfaces
and an explicitly conditional uniqueness theorem, without claiming full
Choquet decomposition.

## Public-source audit

### TailChoquet

The public declarations construct the actual `condExpKernel` on
`FKLimit.tailSigma`, prove composition with the trimmed tail measure, prove
DLR membership a.e. on the fibres, and define the Giry law
`tailLawDistribution`. The individual-event properness theorem has its null
set depending on the event, as its statement says. It is not used here as
simultaneous properness.

Paper Proposition 1.8(1) states the limiting-law property for extremal Gibbs
measures and `ex G ⊆ W`. The public module does not overstate that result. The
remaining non-extremal Choquet input is simultaneous fibre extremality (or an
equivalent simultaneous tail zero-one statement), not another barycenter
identity.

### RightWiredEquationNine

`equation_nine_rightWired` really compares two actual normalized right-wired
FK laws on the interior preimage of an arbitrary finite event. Its RHS is the
actual Bernoulli-product mass of the complement of the canonical maximal
stratum. The good-intersection equality is supplied by a theorem, not a
hypothesis.

Paper Lemma 2.1 instead asserts nested-box marginals for arbitrary
`Λ ⊆ Δ ⊆ Σ`, including the second marginal restricted to `E_Δ`, arbitrary
boundary configurations, and free conditional interiors. The public theorem's
free-left/right-supported split-graph class does not establish those nested
marginals. Calling it full Lemma 2.1 would therefore be invalid; this audit
does not do so.

### AGBoundedRangeImplant

`deviceConfig` means ordinary-bond-open OR existence of an active device whose
support contains the edge. The route theorem replaces traversals of a pivotal
bond by a supplied walk. The annular theorem correctly requires replacement
walks for every source-open enhanced edge removed from the annulus. The
probability constants come from the actual normalized finite independent
product and the existing bounded-fibre transport.

Paper Theorem 1.4 invokes essential-enhancement theory to obtain a strict
critical shift. The public route/annular comparisons do not themselves supply
the required two-path/annular geometry, device-overlap summation, differential
integration, or infinite-volume limit. No such strict shift is claimed here.
The general-geometry concern recorded in the repository is consistent with
Balister--Bollobás--Riordan,
[*Essential enhancements revisited*](https://arxiv.org/abs/1402.0834).

## New declarations

In `FK.InfiniteVolume`:

1. `measurable_compProd_right` proves measurability of `x ↦ f x ⊗ₘ κ`.
   The proof uses `Kernel.measurable_kernel_prodMk_left`; a fixed-set kernel
   evaluation theorem would not suffice because the set section varies with
   the exterior point.
2. `measurable_exteriorMeasure_toMeasure` and `measurable_dlrCompProd`
   specialize that argument to the DLR equation.
3. `measurableSet_eq_of_boolCylinders` shows that equality of measurable
   families of probability laws is a measurable predicate. Only the countable
   family of finite-support Boolean cylinders is intersected.
4. `measurableSet_isDLR` and `measurableSet_dlrMeasures` show that the
   finite-box and full DLR loci are measurable in the Giry space.
5. `ae_mem_dlrMeasures_tailLawDistribution` proves the literal statement

   ```lean
   ∀ᵐ ν ∂(tailLawDistribution μ : Measure
       (ProbabilityMeasure (Configuration E))),
     ν ∈ DLRMeasures exh Φ hq hp
   ```

   given that `μ` is DLR. Measurability of the DLR locus is used to transfer
   the source a.e. statement to the trimmed tail measure and then through the
   Giry map. Thus the mixture really has DLR support, not merely individually
   proved fibre properties with an undocumented measurability gap.
6. `eq_of_ae_isExtremalIn_tailConditionalLaw` proves `μ = μ₀` if every
   extremal probability law in a supplied class is `μ₀` and almost every tail
   fibre is extremal in that class. For each measurable event it transfers an
   evaluation equality using `ae_eq_trim_of_measurable`, then applies the true
   RCP composition identity. It deliberately does not require or pretend to
   have `MeasurableEq (ProbabilityMeasure ...)`.
7. `eq_dlr_of_ae_isExtremal_tailConditionalLaw` is the direct DLR-class
   specialization. Its premises are precisely extremal-DLR uniqueness and
   a.e. extremality of the actual tail fibres in the DLR class.

## Exact residuals

- The new support theorem says nothing about extremal fibres.
- The uniqueness theorem retains a.e. fibre extremality as an explicit
  premise. It does not prove that premise, simultaneous properness on all tail
  events, or a zero-one law for the non-countably-generated tail.
- Consequently arbitrary non-extremal Choquet decomposition and ordinary DLR
  uniqueness from extremal uniqueness remain unfinished in the unconditional
  sense.
- No nested-box Lemma 2.1, general interior weak-limit conversion, global AG
  strict shift, or whole Theorem 1.4/1.9/1.10/1.11 is asserted.

## Verification

Using the repository Elan home `.scratch/elan` and pinned Lean 4.35.0:

- `RightWiredEquationNine.lean`, `AGBoundedRangeImplant.lean`, and
  `TailChoquet.lean` were independently recompiled from source with default
  heartbeats, writing only under this member's `oleans/`.
- `NewestModulesValidation.lean` was independently compiled warning-free with
  default heartbeats, using `-R` for the member package root.
- `ValidationAudit.lean` audited seven public anchors and all nine new
  declarations. Every audit reports exactly `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx` or other axiom occurs.
- Logs and source hashes are in `logs/`. No shared-results source, Git state,
  or GitHub resource was modified.
