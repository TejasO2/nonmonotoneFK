# Ordinary nested FK gluing by pullback fibre wiring

For finite labelled multigraphs, an edge equivalence and a possibly
noninjective surjection compatible with every source/target, this module wires
each vertex fibre by `Setoid.comap g α`. It proves exact wired/open reachability
and connected-component equivalence, followed by component-count and FK-weight
preservation. Consequently `map_gluedConfig_fkPMF` proves exact normalized FK
transport without requiring a vertex equivalence. The inputs $0<q$ and $0<p<1$
are explicit.

`map_nestedSplit_fkPMF` specializes to ordinary nested boxes. The radial
instance constructs the actual small-vertex map and split/outside gluing, with
endpoint identities supplied by the existing metric and split equivalences.
`radialSplitSourceLaw_cross` explicitly relates duplicated small/large vertex
copies, unlike `largeSourceLaw`. `map_radialSplitConfigToBox_fkPMF` and
`radialSplit_real_boxCylinder` prove exact large-box law and finite-cylinder
identities for this new pullback source.

This is distinct from gluing the old no-cross law, whose no-comap obstruction is
unchanged. It supplies no `hgood`, arm inclusion/vanishing, DLR or strong-
uniqueness conclusion for the new source convention.

## Verification

The exact candidate was independently rebuilt using Lean 4.35.0/default
heartbeats. Its 29 principal declarations passed the repository axiom checker,
with only `propext`, `Classical.choice`, and `Quot.sound`; no placeholders,
unsafe declarations or custom axioms occur.
