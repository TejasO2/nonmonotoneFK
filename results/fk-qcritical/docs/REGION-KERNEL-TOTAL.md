# Total arbitrary-event random-region disintegration

Public module: `FK.RegionKernelTotal` (namespace `FK.RandomRegionKernel`).
This extends arbitrary events and almost-finite regions what the earlier
interior/cylinder-only module disintegrated over random closed regions.

For a law meeting the actual exterior-partition DLR equation at *every* finite
vertex box, `predictKernel` glues an exterior configuration with the free FK
box conditioned on the forced interior connectivity. `sliceVal` gives its mass
on any measurable global event. Product decomposition and Fubini prove
`region_kernel_disintegration_total`, where $C$ need not be interior-supported
or a global cylinder. On the attained null strata, conditioning is zero just
as in the finite kernel, with no auxiliary positivity requirement.

`region_kernel_total_univ` adds the global identity when the closed region is
almost surely finite. Dominating a law with the nonpercolating upper coordinate
of a genuine ordered coupling obtains this for any finite base:
`ae_nonPercolating_of_orderedCoupling`, finite open clusters, and the random
closed region's finiteness supply exactly that input.

For the source's free-boundary conditional sentence, the two
`condExp_cylinder_eq_freeMass_of_*` theorems show that at a closed-frontier box,
conditional probabilities of cylinders supported inside it are the free FK
masses of their interior readouts. The stochastic configuration is closed on
the frontier, so the conditional law is the free boundary FK measure rather
than a naive unconditional conditioned box.

## What is still required for Theorem 5.1

This module does not prove uniqueness. In addition to the actual dependency and
regular conditional contexts being matched, comparing two laws needs a
**conditionally independent ordered coupling**, whose fibres over the common
nonpercolating coordinate are themselves ordered. Then one can compare the
conditional terms and invoke tail-trivial/reverse-martingale results. A generic
one-sided stochastic order coupling does not supply the random-region tower
identity, and the new regular region laws alone do not give it.

The convention in the statement is the actual exterior-induced partition at
every finite box, not the entire collection of all conventions. The global
Theorem 5.1 uniqueness assembly, weak-limit Prop. 1.8(2), and any FK-window or
strong-planar conclusion remain open.

The exact file was independently rebuilt against public imports with pinned
Lean 4.35. All 12 principal axiom reports contain only standard axioms.
