# Dual-parameter equation (12) and DLR transport

Public module: `FK.DualParameterDuality` (namespace
`FK.InfiniteVolume`). This instantiates the finite measure duality of
`equation_twelve_actual` in the `FiniteBox` framework, with the **paper's dual
parameter**, rather than claiming the earlier generic same-parameter transport
already supplied that application.

## Relabelling normalized finite FK measures

`componentCount_reindex_apply` generalizes the public free-boundary component
count invariance to an **arbitrary** boundary setoid.
`edgeWeight_reindex`, `fkWeight_reindex`, `partitionFunction_reindex` and
`fkPMF_reindex` carry the edge weight, FK weight, total normalization and
normalized PMF through an edge equivalence. `normalizedPMFOfSumPos_equiv` is
the corresponding elementary fact about normalized positive finite families.

`sumEdges I O` and `sumEdgesEquiv` identify the interior label type `I` with
the corresponding subtype of global `I ⊕ O`. `planeBox_graph` is definitionally
the `interiorOfSum` graph reindexed along this identification, so
`planeBox_fkPMF` reduces the box normalization to that model's normalization,
with the same arbitrary boundary setoid preserved.

## Dual parameter and source conventions

With $p'=p/(p+q(1-p))$, the transported parameter is
$p^*=q(1-p)/(p+q(1-p))=1-p'$.

`coe_dualParameter_eq_one_sub_prime` exposes this relation. The
`dualParameter_le_one` interval proof is supplied by the existing finite-plane
API, not by a bogus renaming of $p$.

`primalConvention` is the primal exterior open-component partition. The dual
convention is its counterpart for the dual exterior graph, using the provided
exterior edge identification. `dualConfig_planeExterior` identifies the latter
with the dual configuration used by `equation_twelve_actual`. `measurable_primalConvention`
and `measurable_dualConvention` discharge the measurability obligations, so
those are no longer inputs of the box theorem. The remaining geometric input
is exactly the Euler component relation `heuler` required by the finite fact.

## Proved results

`planeBox_pmf_dualParameter` proves equation (12) in box PMF language, by
calling `equation_twelve_actual` at the correct graph and exterior data.
`kernel_dual_of_pmf_dual_dualParameter` converts it to the dual-kernel identity,
and `isDLR_map_cfgDual_dualParameter` transports a genuine `(q,p)` DLR law to
the `(q,p^*)` one for a primal/dual `FiniteBox`. The resulting
`isDLR_map_cfgDual_equation_twelve` uses the actual source exterior
conventions, and `eq_map_of_unique_dual_equation_twelve` gives the singleton
implication: if the dual one-box DLR class is `{ν}`, then the primal law is the
complement of ν.

This is a conditional one-box singleton adapter, not the existence of global
uniqueness for every convention or a theorem of planar cluster separation.

## Deliberate remaining scope

No primal at-most-one-cluster conclusion is inferred. Endpoints `p=0,1` are not
handled, nor reverse dual-to-primal transport, an infinite/cofinal boundary
lift, a continuous embedding, a rotation-system certificate or graph-local
finiteness. Those and the enhanced reference-phase shift must still be built
before Theorem 1.11 can be called proved. The source Euler relation remains
input; it is not silently generated from `dualBox`.

The exact source was independently rebuilt under pinned Lean 4.35/default
heartbeats. Its 21 principal axiom reports use only `propext`,
`Classical.choice` and `Quot.sound`, without proof holes or trust overrides.
Four unused-instance/simp proof-linter warnings remain non-semantic.
