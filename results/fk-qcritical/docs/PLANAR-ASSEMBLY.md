# Exterior determination and planar uniqueness assembly

Public modules: `FK.FiniteExteriorDetermination`, `FK.PlanarGlobalAssembly`,
`FK.PlanarAEKernelDuality`, and `FK.PlanarAllBoxDuality`.

This package supplies finite-window and probabilistic ingredients for the
Theorem 1.11 argument. It does **not** prove the full theorem: the general
enclosing-circuit construction, finite planar duality instantiation, and
essential-enhancement phase bounds remain separate mathematical inputs.

## Finite-window convention determination

`exists_exhaustion_box_determining_convention` produces one genuine exhaustion
box whose edge restriction determines every geometric boundary convention at
an at-most-one-infinite-cluster configuration. The finite support includes a
chosen open path for every connected pair of boundary roots and the entire
incident-edge support of every finite component of a boundary root.

For a disconnected pair, at most one infinite component forces at least one
side to be finite. Arbitrary edits away from the support therefore cannot
change the partition. This is an explicit finite strengthening of the existing
local-constancy theorem, for the free component setoid as well as every
convention satisfying merge/finite-separation.

## Cluster and phase assembly

`ae_exactlyOneInfiniteCluster_of_primal_bernoulliProduct_stochDom` takes an
actual inhomogeneous Bernoulli lower bound for the primal law, exact
complemented dual Bernoulli nonpercolation, primal Bernoulli supercriticality,
and the geometric premise `DualNonpercolationForcesPrimalAtMostOne`. It proves
almost-sure `ExactlyOneInfiniteCluster`, the conjunction of having an infinite
cluster and at-most-one infinite cluster. The two stochastic-order directions
are kept explicit: lower bounds transfer full-mass increasing events, while
upper bounds transfer null infinite-cluster events.

The geometric premise is not proved here. Bare graph duality does not supply it
in general, as the existing strip counterexample demonstrates.

## Almost-everywhere and all-box dual transport

`isDLR_map_cfgDual_core_ae` uses genuine `Measure.compProd_congr` equality, so
finite planar kernel duality is needed only on full-measure exterior fibres of
the complemented law. No convention is assigned arbitrarily on the null set,
and no DLR property is assumed for those bad fibres. Dual-parameter,
single-box, and arbitrary family versions are included.

`isDLR_freeComponents_of_globalAtMostOne` uses interior finite-volume full
support to replace every coherent geometric source-convention DLR equation by
the canonical free exterior-component equation at every finite box. Combined
with the almost-everywhere kernel theorem, this removes the older requirement
that every original source convention individually be dualizable. Equation (12)
is now needed only for the free representative and only on relevant
full-measure exterior fibres.

The wrapper `eq_dual_and_ae_exactlyOne_of_allBoxes_of_ae` derives global
at-most-one from the phase inputs, identifies each qualifying all-box source
DLR law as the complement of the unique dual law, and proves almost-sure exact
one infinite primal cluster.

## Explicit remaining obligations

That wrapper deliberately retains:

1. the actual planar geometry premise forcing primal at-most-one from dual
   nonpercolation;
2. the finite planar equation (12) for the free representative, with its
   Euler/incidence construction;
3. uniqueness of the dual all-box DLR class;
4. the enhanced inhomogeneous lower bound, complemented dual nonpercolation,
   and primal supercriticality;
5. a coherent all-box DLR law with interior `0 < p < 1` and `0 < q`.

Thus these modules close finite-window replacement, almost-everywhere dual
transport, and all-box cluster-count assembly. They do not supply general
Jordan circuits, AG, Theorem 1.10, unrestricted arbitrary-setoid Proposition
1.8(2), or endpoint rates. The source-union Proposition 1.8(2) needed to
promote a general weak-limit input to the coherent DLR class is proved
separately in `FK.FreeNestedGeometry`.
