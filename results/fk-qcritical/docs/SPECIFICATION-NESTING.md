# Finite FK specification nesting and conditional ratios

Public module: `FK.SpecificationNesting` (namespace
`FK.Finite.SpecificationNesting`). It supplies the generalized finite
"standard computation" behind an FK specification: an arbitrary vertex region,
an arbitrary set of interior labelled edges and an arbitrary boundary setoid.

The key graph `fixedGraph` closes all interior edges but retains outside edges
and the ambient wiring. `inducedPartition` is reachability in this graph on the
region. `componentCount_split_subBox` counts components in the ambient model,
the induced classes and the sub-box exactly: region components merge only
through already-existing exterior paths/wiring, while ordinary interior edges
remain available. The edge-weight and $q$-power product then factors over the
split edge types. This yields both weight-level conditional normalization and
`fkPMF_conditional_ratio`, for *every* exterior configuration.

The proof uses no `hgood`, probability coupling, graph planarity, limit model,
`hAG`, custom axiom or proof placeholder. `inducedPartition_combine_eq` shows
that only the exterior configuration matters;
`exteriorReachable_inducedPartition` proves the expected exterior-path
compatibility.

## What is still unfinished

This is a finite ratio theorem, not yet an assertion of
`BoundaryConvention.compatible` across an exhaustion or Prop. 1.8(2). The
conditional-PMF/filter and `FiniteBox.IsDLR` packaging still has to be put in
that form. `BoxExhaustion` records edge-set nesting, not the vertex-level
nesting and annuli needed to state a literal convention compatibility without
more geometry (region boxes are one available model). Once these are supplied,
the paper's weak-limit convention bridge remains a separate task.

The ten principal axiom reports use only standard foundational axioms, and the
exact source was independently rebuilt against `FK.FiniteModel`.
