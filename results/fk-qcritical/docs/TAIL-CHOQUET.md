# Tail regular-conditional decomposition (direction A)

## Proved

The Lean development in `TailChoquet.lean` uses no extremality hypothesis.
For a countable edge type and a probability law `μ` on Boolean edge
configurations:

* `tailConditionalKernel` is the actual
  `ProbabilityTheory.condExpKernel μ FKLimit.tailSigma`, not a postulated
  component family.
* `tailConditionalKernel_comp_trim` proves that it mixes back to `μ`.
* `dlrReconstructionKernel` resamples a finite box by the actual FK kernel,
  with the exterior marginal retained.
* `ae_dlrReconstructionKernel_tail` proves equality of a tail fibre and its FK
  reconstruction on any fixed measurable event.  The proof uses the diagonal
  disintegration identity on arbitrary tail test sets and the exact exterior
  support of `FiniteBox.conditionalLaw`.
* `ae_isDLR_tailConditionalLaw` intersects countably many finite Boolean
  cylinders and obtains the full finite-box `IsDLR` equation almost surely.
  It assumes only the original DLR equation with its arbitrary measurable
  exterior-dependent boundary partition.  No nesting compatibility or local
  constancy is needed.
* `ae_mem_dlrMeasures_tailConditionalLaw` upgrades this to every box of an
  exhaustion simultaneously.
* `tailLawDistribution` pushes the tail index law forward to the genuine Giry
  space `ProbabilityMeasure (Configuration E)`.
  `lintegral_tailLawDistribution` proves the exact barycenter identity on
  every measurable event.
* `ae_tailConditionalKernel_apply_tail` proves properness on one tail event,
  with the null set depending on that event.

## Precise residual hypothesis

This is not claimed as the full non-extremal Choquet theorem.  The missing
statement is simultaneous tail zero-one/extremality of almost every fibre.
The tail sigma-algebra is not assumed countably generated, and the individual
properness null sets cannot simply be intersected.  Accordingly,
`ae_mem_fkLimitMeasures_tailConditionalLaw_of_extremal` assumes the missing
`FK.IsExtremalIn` property at the fibre before invoking the existing
`mem_fkLimitMeasures_of_extremal_dlr`.  No non-extremal weak-limit conclusion
is asserted without that hypothesis.

## Verification

Built with the repository's Lean 4.35.0 toolchain and project-local Elan
using `lake env lean` on this file.  `TailChoquetWithAudit.lean` appends
standard `#print axioms` checks; `TailChoquet.audit.txt` records the output.
The eight principal declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The source has no
`sorry`/`admit`/`unsafe` or new axioms.
