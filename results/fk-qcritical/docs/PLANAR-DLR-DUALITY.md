# Conditional DLR transport under planar configuration duality

Public module: `FK.PlanarDLRDuality` (namespace `FK.InfiniteVolume`).
This supplies reusable **measure-transport** lemmas for configuration
complementation. It is not a completed application of equation (12), and is not
Theorem 1.11.

## Generic configuration and box duality

`cfgDual E` complements all global edge bits. `intDual B` and `extDual B`
complement the interior and exterior coordinates of a finite labelled box.
They are measurable involutions, and `split_cfgDual` proves that
complementation commutes with the box split. `dualBox B Vd s t` uses the same
global labels and an explicitly supplied dual vertex/endpoint structure; it
does not itself construct a plane embedding or a genuine plane dual.

The separately available `componentCount_reindex` and `openCard_reindex`
preserve the boundary-free component and open-edge counts under an equivalence
of labelled edge types. These can be used to reindex the finite Euler relation
between edge-subtype models and global labelled pairs.

## What is proved for the DLR equation

For any primal DLR law, `isDLR_map_cfgDual_core` transports its exact
composition-product equation across configuration complementation, given a
Markov kernel that is the pointwise complement of the original box kernel.
The helper `map_prod_map_compProd` identifies the resulting composition product
and its exterior marginal, rather than merely giving abstract measure
inequalities. `compProd_singleton` handles singleton fibres.

`isDLR_map_cfgDual` specializes this to a supplied `dualBox` while `hk` asserts
its actual FK kernel relation; the primal and dual FK parameters are simply
the parameters chosen for each side in that invocation.

`kernel_dual_of_pmf_dual` derives `hk` from an explicit PMF identity over every
exterior configuration, and `isDLR_map_cfgDual_of_pmf` combines the two steps.
The provided `hpmf` is thus a **general, quantified normalized-PMF hypothesis**
about the supplied matching setup, not an already-established theorem about a
general plane dual graph with arbitrary boundary conditions.

If the dual one-box DLR class is singleton, `eq_map_of_unique_dual` forces the
corresponding primal law to be the image under `cfgDual`. This is a conditional
singleton adapter for the displayed one-box data, not uniqueness for every
convention, all finite boxes, or an infinite FK family.

## Precise remaining equation-(12) instantiation

`FK.FinitePlane.equation_twelve_actual`, in `FK.PlanarActual`, is *not*
instantiated in this module. In that theorem the dual FK parameter is obtained
through `dualParameter`, the underlying models are `ambientOfSum` and
`interiorOfSum`, and the boundary setoids are the matching `exteriorBoundary`
relations for the corresponding edge equivalences. The eventual application
in the paper also needs the exterior configuration to have at most one
infinite cluster. These quantifier orderings, view changes and geometric
conditions must all be transported, not ignored.

Accordingly, the following remain work outside this package:

* a correct reindexing between region boxes and the ambient/interior models,
* the supplied `GraphicDualCertificate` and free-graph Euler hypotheses,
* the dual parameter and matched exterior-boundary assignments,
* the actual global uniqueness presumed by the singleton adapter,
* strict essential-enhancement shifts used on the dual graph,
* Theorem 1.10/Theorem 5.1 and Proposition 1.8(2), and
* finite dual nonpercolation implying at most one infinite primal component.

These are not replaced by a new labelled-dual-box definition or a conditional
DLR identity.

## Verification

The submitted exact source was independently rebuilt with pinned Lean 4.35
and current public imports. Its four principal axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`. No proof placeholder, custom
axiom, unsafe declaration, `native_decide` or trust override was found.
Integration removes unused simp/tactic spelling without changing statements.
