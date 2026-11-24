# Nested exterior mixtures and growing-vertex free FK limits

Public aggregate: `FK.NestedMixture`. The eight component modules are in
`FK/NestedMixture/` and use namespace `FK.NestedMixture`. This development proves
normalized nested finite-FK conditioning and a genuine growing-vertex free-limit
existence theorem at $q\ge1$. It does not prove uniqueness or a wired-family
limit.

## The exact exterior mixture

For a finite labelled multigraph, choose an interior vertex region and interior
edge set whose endpoints lie in that region. `Mixture.lean` identifies the
larger FK law restricted to the inner edges as a mixture of sub-box FK laws at
the exterior-induced boundary partitions, weighted by the realized exterior
configuration.

`fkPMF_combine_eq_fibreWeight_mul` is the pointwise factorization
`joint = exteriorFibreMass * innerFKMass`. Its proof does **not** divide by an
arbitrary fibre mass: it applies `SpecificationNesting.fkPMF_conditional_ratio`,
multiplies the identity through, then sums over all inner configurations using
the sub-box law's normalization. The exterior fibre weights themselves sum to
one after reindexing along the interior/exterior configuration equivalence.
There is therefore no hidden fibre-positivity implausibility.

For every interior event,
`fkMeasure_cyl_eq_mixture` reindexes that exact sum into a genuine exterior
mixture. At $q\ge1$, free/wired monotonicity of each fibre yields the lower
and upper bounds for increasing events (`fkMeasure_cyl_ge_free` and
`fkMeasure_cyl_le_wired`). The mixture identity itself needs only $q>0$ and
interior $p$.

## Genuine nested graph data

`Transport.lean` proves pointwise mass and measure identities for the free FK
law under labelled-graph transport, based on the public component-count and
weight transport APIs. `NestedBox.lean` then gives an actual nested pair of
finite boxes: inclusion of edge labels plus an injective vertex map preserving
both endpoints of every small-box edge. A bare `BoxExhaustion` does not supply
these geometric data.

`NestedBox` identifies the corresponding region sub-box with a transport of the
small graph, so its free masses are unchanged. `Compare.lean` combines that with
the normalized exterior mixture to prove

$$\phi_B^{\mathrm{free}}(A)\le
  \phi_C^{\mathrm{free}}(x\vert_{\mathrm{inner}}\in\mathrm{cyl}(A))$$

for every increasing small-box event at $q\ge1$. The same inequality holds with
any setoid on the large graph, including a boundary-wired one.

## Full-sequence free limits

`Limit.lean` packages a `GrowingFamily` of boxes with covering nested edges and
the paired nesting data. Its `upT` masses are eventually monotone by the
nested-event comparison, so the already verified
`MonotoneLimitExistence.exists_isFKLimit_of_eventually_mono_upT` yields an actual
weak limit of the entire free finite-volume sequence
(`GrowingFamily.exists_free_limit`). This is not merely compactness-selected
subsequence existence.

`Example.lean` instantiates the structure for a family of parallel loops.
`PathFamily.lean` proves a more substantive nonvacuity instance: on the natural
number line the boxes use `Fin (n+1)` vertices and edges `i ↦ (i,i+1)`, with
order embeddings preserving endpoints. Both vertices and edges genuinely grow;
the free path-box laws therefore have a full-sequence limit at interior $p$.

`BoundaryConvention.lean` defines the boundary-only setoid by
$x\sim y\iff x=y\lor(x,y\in bnd)$. It is between the free and all-vertex-top
class, giving its FK sandwich at $q\ge1$. This corrects the temptation to use
the vacuous all-vertex top setoid as the paper's boundary-wired law.

## Remaining scope

No concrete $\mathbb Z^d$ box/boundary-field presentation is constructed yet.
Wired-family transport and upper-coordinate cross-scale comparisons are not
supplied, and the free-limit path is not asserted to give a unique or canonical
DLR law. The growing-family geometric data are not a hidden measure-theoretic
premise, but they must still be constructed for the desired quasi-transitive
graph. No Theorem 1.4, 1.9, 1.10, 1.11, 5.1 or Prop 1.8(2) conclusion follows.

All eight exact sources and their 23 principal axiom reports were independently
checked under Lean 4.35.0 and default heartbeats. Only `propext`,
`Classical.choice`, and `Quot.sound` appear; warnings are nonsemantic lints.
