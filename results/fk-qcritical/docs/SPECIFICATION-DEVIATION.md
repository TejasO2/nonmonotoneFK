# DLR specification deviation and a uniqueness reduction

Public module: `FK.SpecificationDeviation` (namespace `FK.InfiniteVolume`).
It isolates the common specification integral behind two DLR laws and proves a
mean-insensitivity criterion for uniqueness. It is not a complete proof of
Theorem 5.1 and does not implement the random-fibre martingale argument.

## A law-independent common integrand

For an actual DLR law $\mu$ on a box and event $A$ supported on its edges,
`apply_eq_integral_conditionalLaw_real` proves

$$\mu(A)=\int \operatorname{specValue}(B,\alpha,\omega,A)\,d\mu(\omega),$$

where `specValue` is the box conditional FK law evaluated at the observed
exterior. This uses the actual DLR equation and preservation of conditional
expectation under integration; it is the same integrand for every DLR law of
that convention, with no common joint coupling required. A variant computes
the mass directly for a constant boundary partition and then for a whole
exhaustion.

`specValue_eq_fkMeasure` relates this value to the normalized finite FK
measure; `refValue` is the corresponding closed-exterior value.
`abs_apply_sub_refValue_le` bounds the deviation of one law's mass from that
reference by the mean deviation of its specification. Taking two laws gives
the quantitative bound in `abs_apply_sub_apply_le_deviation`.

Consequently, if the mean deviations vanish along the exhaustion for both laws,
they agree on each supported event and therefore
(`probabilityMeasure_eq_of_tendsto_deviation`) coincide.
`not_tendsto_deviation_of_ne` contraposes that result: non-uniqueness forces
boundary sensitivity. These obligations are about the specification, not a
hidden equality-of-measures hypothesis.

## Cylinders and increasing events

An explicit `cylinderEvents` π-system generates the product σ-algebra, so
`measure_eq_of_forall_dependsOn` (and `exists_dependsOn_real_ne` for cylinder
separation) identifies probability measures from finite-support event masses.
The mean-deviation criterion increases this to all cylinders.

On increasing box events at $q\ge1$, the normalized free/wired comparison
bounds the deviation from free mass by the free/wired gap
(`real_bounds_of_free_wired_sandwich`, `abs_specValue_sub_free_le_gap`). Upper
corners `upT` recover true-set cylinders by finite induction;
`measure_eq_of_cyT_eq` then recovers an arbitrary supported event as a disjoint
union of patterns. Therefore
`probabilityMeasure_eq_of_tendsto_deviation_increasing` requires the mean
insensitivity only on increasing finite-support events.

The `specValue_eq_refValue_of_closed_exterior` result records the deterministic
part of the ordered coupling: if a convention assigns its reference partition
whenever a finite edge set is closed, then $\xi\le\eta$ with $\eta$ closed on
that set puts $\xi$ in the same fibre. No probability or net theorem enters
that fact.

## Unconditional special cases and remaining input

`probabilityMeasure_eq_of_const_partition` proves singleton DLR classes for a
convention whose partition does not depend on the exterior. The special case
`probabilityMeasure_eq_of_free_convention` is for an actually constant discrete
boundary assignment. It is **not** the source's free convention, whose exterior
open-component partition varies with the configuration, and it supplies no
nonpercolation statement.

The actual domination proof still needs the relevant finite-volume or regime-
specific gap to vanish, and a way from increasing events back to arbitrary
cylinders where the parameter regime reverses wiring order. No proof of that
gap, of the joint random exhaustion, or of Theorem 5.1 is asserted. Other
paper theorems, AG geometry and source-faithful DLR existence are likewise
untouched.

The exact source was independently rebuilt with pinned Lean 4.35.0 at default
heartbeats. Its 19 principal axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.
