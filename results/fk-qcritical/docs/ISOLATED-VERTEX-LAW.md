# Isolated-vertex invariance of normalized finite FK laws

Public module: `FK.IsolatedVertexLaw`. This supplies the missing isolated-vertex
measure transport for finite FK models, including the genuine `FiniteBox` and
`finiteVolumeLaw` forms.

## Meaning of the invariance

Take a labelled multigraph on a finite vertex type $V$ and the same labelled
edges on $V\oplus X$, with sources and targets sent into the left summand by
`Sum.inl`. The configuration space is literally the same $E\to\mathsf{Bool}$.
The boundary is `setoidSumInl ξ X`: it carries an arbitrary $\xi$ on $V$ and
places each new vertex in singleton blocks.

The proof gives exactly

$$
\kappa_{\xi'}(\omega)=\kappa_\xi(\omega)+|X|,
\qquad w'(\omega)=w(\omega)q^{|X|},
\qquad Z'=Zq^{|X|},
$$

so the normalized PMFs and measures are **equal** on $E\to\mathsf{Bool}$. The
only needed parameter conditions are $q>0$ and $p\le1$; endpoints $p=0,1$ are
included. Free boundary is the special $\xi=\bot$ case.

The underlying graph argument is not an informal appeal to isolated points:
`inducedConnectionIso` identifies the induced extended connection graph on the
old vertices with the old connection graph. Open edges only occur on the left,
and no boundary relation touches the right. The accepted isolated-component
formula then yields the extra $|X|$ components.

This uses the common constant shift to cancel normalization, so it is not merely
transport of raw weights or an identification after imposing an external
conditional.

## Genuine box form

`FiniteBox.extendVertices X` retains the same global edge labels and carries all
endpoints by `Sum.inl`. Its `Interior` and `interiorRestriction` are unchanged,
and `interiorFKMeasure_extendVertices` identifies the interior laws.

The actual `finiteVolumeLaw` measures also agree globally:

$$
(B.\mathrm{extendVertices}\;X).\mathrm{law}
 = B.\mathrm{law}.
$$

Furthermore, `fkMeasure_le_of_inj_sumInl` composes the existing edge-injection
comparison with this invariance so that one can compare directly with its
augmented graph. That application still requires its `PosAssoc` input.

## Why the new vertices must be free

A wired new vertex changes the component count in a configuration-dependent way,
so the normalization cannot cancel. The module computes this exactly for the
one-edge graph using `Unit → Bool`, with two real vertices on the left and one
additional vertex. At $q=2$ and $p=1/2$, the wired extended law gives all-closed
mass $1/2$, while the free two-vertex law gives $2/3$. The measures are therefore
unequal. `componentCount_shift_fails_wired` records the corresponding wrong
component-count shift.

## Remaining obligations

There is no `PosAssoc` instantiation, stage-monotonicity theorem, concrete
exhaustion identification, or no-mass-escape conclusion here. The edge-injection
API inherits the `fgOf` `Type 0` edge-type limitation; vertices are otherwise
universe-polymorphic. The identified free/carry-boundary law does not authorize
arbitrary cross-wiring.

The remaining work is to discharge association from `WiredFKG` and prove the
stage estimate on the actual nested far-connection events.

## Verification

The exact candidate was rebuilt and all 16 fully qualified principal
declarations audited on Lean 4.35/default heartbeats against current public
imports. Every audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. Run `./check.sh` for the complete release verification.
