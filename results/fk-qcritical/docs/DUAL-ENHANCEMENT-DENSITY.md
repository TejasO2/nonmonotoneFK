# Theorem 1.11 dual-enhancement density bridge

Public module: `FK.DualEnhancementDensity`.

This is a new graph-theoretic component of the proof of Theorem 1.11. It
transports the bounded-distance condition on an enhanced edge set from the
primal line graph to the dual line graph **without assuming quasi-transitivity
of the dual graph**.

It is not Theorem 1.11 or a dual form of Theorem 1.10. The primal and dual
models here are `SimpleGraph`s related by an actual edge equivalence.
Consequently loops and parallel edges of a general source planar multigraph
dual remain outside this file's scope. No arbitrary continuous plane embedding
is constructed.

## Principal result

The source-shaped declaration is
`FK.Planar.DualEnhancement.boundedDistance_image_of_paperHypotheses`.
Its inputs are:

- `FK.AGShift.PaperGraphHypotheses G o` on the **primal** graph;
- an edge equivalence `edge : G.edgeSet ≃ GD.edgeSet`;
- `VertexCornerBound edge (fun v => G.degree v)`, meaning that the two dual
  edges corresponding to incident primal edges at `v` are reachable in the
  dual line graph at distance at most the primal degree of `v`;
- `FK.Theorem14.BoundedDistance G.lineGraph.dist S`.

Its conclusion is exactly

```lean
FK.Theorem14.BoundedDistance GD.lineGraph.dist (edge '' S)
```

There is no hypothesis or conclusion involving dual quasi-transitivity, dual
bounded-degree bounds, dual cycle/double-ray existence, the dual critical
probability, AG, nested equation (9), finite-volume FK duality or strong
uniqueness.

## Mathematical argument

A finite rotation system supplies a local corner path around a vertex. The
primal quasi-transitive degree bound makes the resulting local bound uniform.
For a uniform bound $K$, telescoping local dual-distance estimates along a
primal line-graph walk yields

$$\operatorname{dist}_{G^*,\mathrm{line}}(\mathrm{edge}(e),\mathrm{edge}(f))
  \le K\operatorname{length}(w).$$

Taking a shortest walk proves `UniformCornerBound.dist_map_le_mul`.
`lipschitz_iff_uniformCornerBound` proves the converse, so the local condition
is exactly equivalent to this Lipschitz/reachability estimate. If every primal
edge is within distance $R$ of $S$, every dual edge is within distance $KR$ of
its image. Corner links and a connected primal line graph also imply dual
line-graph connectedness.

`uniformCornerBound_refl` verifies non-vacuity on the identity edge pairing.

## Source audit and remaining gaps

Section 5.2 of the paper applies essential enhancements to the geometric dual
and later invokes Theorem 1.10 there, although Theorem 1.11 adds only the plane
embedding and dual local finiteness. This density step avoids requiring dual
quasi-transitivity. The direction comparison in the paper also has useful
algebraic content:

- for $q<1$, primal lower-star devices have the labels needed for dual cycle
  devices;
- for $q>1$, primal lower-cycle devices have the labels needed for dual star
  devices.

This module proves only density, not the actual finite-device dualization.

The following remain open:

1. construct the local corner/rotation data for a source embedding, including
   multigraph incidence where required;
2. dualize the finite star/cycle comparison devices while retaining
   auxiliary-free and finite-volume measure identities;
3. establish dual essentialness, rather than merely primal double-ray status;
4. supply the dual critical bounds, AG shift and nested equation (9), exact
   planar at-most-one geometry, and the final uniqueness assembly.

Thus the audit identifies a remaining proof obligation, not a counterexample
to the paper's statement.

## Verification

The five principal declaration audits are in `Audit.lean`. Fresh Lean 4.35
compilation reports only `propext`, `Classical.choice`, and `Quot.sound`, with
no placeholders, unsafe declarations, custom axioms or option overrides.
Run `./check.sh` from `results/fk-qcritical`.
