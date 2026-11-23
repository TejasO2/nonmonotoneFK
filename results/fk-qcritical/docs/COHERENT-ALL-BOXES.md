# Coherent FK specifications on all finite boxes

## Exact result

`CoherentAllBoxes.lean` introduces an actual Markov kernel
`conditionalLawKernel` of global finite-box FK conditional laws in their exterior
configurations. An `AllBoxConvention` supplies a measurable boundary partition
for every finite labelled box and the exact FK compatibility equation for every
nested pair. `AllBoxDLRMeasures` requires the global DLR equation at every finite
box.

The main general step, `isDLR_of_isDLR_of_compatible`, identifies a global law
with the mixture of the larger-box exterior conditional laws induced by its DLR
equation, and applies the accepted DLR mixture theorem. Consequently
`mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction` proves that for such a
convention, testing any genuine exhaustion is equivalent to testing every finite
box. This uses eventual containment and all-pair compatibility; it does not
construct those inputs.

The module also supplies exterior geometry and simple-graph box embeddings for
every finite box, their faithful restriction to one exhaustion, all-box
geometric convention transport under limit-a.e. `GlobalAtMostOne`, coherent
arbitrary-exterior conditional-limit closure, and fixed-specification DLR weak
closure for arbitrary nontrivial filters.

`CoherentAllBoxesAdapters.lean` adds seven consequences:

1. `mem_gibbsMeasures_restriction_iff`: the exhaustion chosen to test a fixed
   all-box convention is immaterial.
2. `mem_allBoxDLRMeasures_of_tendsto_finiteVolumeLaw_of_globalAtMostOne_of_le_one`:
   closed-exterior finite-volume laws on one genuine graph exhaustion converge
   to a law in the target all-box class, under the stated geometry and global
   uniqueness assumptions.
3. `mem_allBoxDLRMeasures_self_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one`:
   fixed-convention arbitrary-exterior conditional-limit specialization.
4. `mem_allBoxDLRMeasures_of_tendsto_conditionalLaw_zero` and
   `..._one`: arbitrary-exterior coherent weak limits at $p=0$ and $p=1$ belong
   to every coherent all-box target class.
5. `mem_allBoxDLRMeasures_of_tendsto_dlr_zero` and `..._one`: the corresponding
   nontrivial-filter weak closures of coherent all-box DLR laws.

The endpoint results follow from the established exact all-closed/all-open
point-mass identifications, not from interior finite-energy arguments.

## Scope and remaining obligations

This is a coherent-specification interface and closure theorem, not a proof that
an arbitrary noncoherent fixed-source weak limit is DLR. No `AllBoxConvention`,
geometric certificate, exhaustion, weak limit, or global-uniqueness hypothesis
is constructed by these files. At interior rates the theorems retain countable
local finiteness, actual weak convergence, both geometric certificates, and
almost-everywhere global at-most-one-cluster uniqueness as stated. At $p=0$ or
$p=1$, those extra geometric inputs are unnecessary because the limit is
deterministic. All-pair compatibility remains an explicit hypothesis even when
an exhaustion is sufficient for testing a convention.

There is no uniqueness-existence assertion, completion of unrestricted
Proposition 1.8(2), or main-theorem completion here. The one-edge noncoherent
counterexample remains in force.

## Verification

Before integration both exact candidate sources were independently rebuilt with
pinned Lean 4.35.0 and default heartbeats. All 26 principal declarations were
then audited separately; every audit used only `propext`, `Classical.choice`,
and `Quot.sound`. Release imports and exact public axiom audits are included in
the full project check.
