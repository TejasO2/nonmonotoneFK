# Nested conditional reverse and Choquet assembly

## Delivered declarations

`NestedConditionalAssembly.lean` (to be integrated as `FK/NestedConditionalAssembly.lean`) imports the public integrated modules
`FK.NestedFiniteAssembly` and `FK.NestedBoundaryUniqueness` and proves:

* `HasVanishingNestedExteriorCouplingError`: an outer/inner two-scale
  conditional-cylinder interface. Its error is indexed by the finite cylinder
  base, as required by the base-dependent roots and widths in the arm events.
* `eq_of_extremal_dlr_of_hasVanishingNestedExteriorCouplingError`: composes
  the actual a.e. reverse conditional convergence with both index maps and
  uses the vanishing estimate to identify every finite-base cylinder.
* `eq_dlr_of_pairwise_hasVanishingNestedExteriorCouplingError`: applies the
  existing tail-fibre Choquet argument, allowing different outer/inner index
  maps for each extremal pair.
* `hasVanishingNestedExteriorCouplingError_of_finiteVolume_farConnection`:
  uses the product of the two global configuration measures, proves its two
  pushforwards, converts closed-exterior finite-volume masses to the actual
  exterior conditional kernels once the cylinder is supported in each box,
  and obtains vanishing errors from nonpercolation via the existing genuine
  far-connection/one-arm estimate.
* `conditionalLaw_cylinder_abs_sub_le_farConnection_of_good`: transports the
  actual single-scale `NestedFiniteAssembly` bound to arbitrary exterior
  conditional laws. The finite `hgood`, `hD`, `hU`, reindexing and cylinder
  support premises remain visible.
* `eq_dlr_of_pairwise_finiteVolume_farConnection`: end-to-end DLR equality
  from pairwise *finite-volume* far-connection bounds, not from an assumed
  vanishing conditional bound.

## Exact residual scope

The last theorem is for two members of the same fixed `DLRMeasures exh Φ`
class. For each pair of extremal members it still requires outer/inner maps
 tending to infinity and the displayed eventual finite-volume arm bound on
the product law. It also requires a connected locally finite countable graph,
an upper product law which is almost-surely nonpercolating, and finite roots,
centers and widths satisfying the stated metric bound. Supplying that bound
through the single-scale theorem still requires the actual nested graph data,
edge compatibility, `hgood`, `hD`, `hU`, and interior `0 < p < 1`. The reverse
and Choquet layers themselves allow `p <= 1`.

This does **not** discharge the common-upper `hgood`, construct the eventual
nested indices or geometry, prove noncoherent fixed-source DLR membership, or
claim full Theorem 1.9/1.10. It supplies the conditional reverse and Choquet
assembly exactly up to those separately scoped inputs.

## Verification

From this member directory, using Lean 4.35.0 and the integrated project's
dependency environment, both targets were elaborated with
`-DwarningAsError=true`:

```text
NestedConditionalAssembly.lean
AuditNestedConditionalAssembly.lean
```

The member audit imports `NestedConditionalAssembly` and prints axioms for all six
declarations. Every result is exactly:
`[propext, Classical.choice, Quot.sound]`.
