# Connected generalized-theta spherical windows

## Deliverable and exact scope

`GeneralizedThetaWindow.lean` is a 449-line module using only the public imports
`FK.GeneralizedTheta`, `FK.JordanUnicyclicEnclosure`, and
`FK.FacialSubdivision`. No unaccepted handoff is imported. Base revision:
`bc165faf5edd9ce57bd655f2ce23884c977b17b0`.

For a finite branch type `ι` and distinct `i,j : ι`, the selected set
`branch i ∪ branch j` is proved to be an exact cycle-matroid circuit of the
accepted `lengthTwoTheta ι`. At scale `a > 0`, the two terminals are at
`(-a/2,0)` and `(a/2,0)`, the selected internal vertices are at `(0,a)` and
`(0,-a)`, and every other internal vertex is at the origin. The selected
straight segments run between terminals and the two exterior vertices.

The principal generic results are:

- `isCircuit_selectedBranches`: the two selected full branches are exactly a
  matroid circuit.
- `crossing_selectedBranches`: every arc meeting the sphere centred at zero of
  radius `3*a/4` has its simple-edge label in the selected circuit. Unselected
  arcs lie in the closed ball of radius `a/2`; this is a proved metric estimate,
  not a supplied crossing hypothesis.
- `exists_branchArc_crossing`: each selected segment genuinely meets that
  sphere, using the inside-to-outside intermediate-value crossing theorem.
- `sphericalOpenCircuit_selectedBranches`: the selected labels form an actual
  `SphericalOpenCircuit`. Their openness comes from `selectedConfig`, and their
  carrier is genuinely open-connected by the existing matroid-circuit transport.
- `preconnected_simpleGraph`: the underlying generalized-theta simple graph is
  connected.
- `finite_vertex_preimage_ball`: finite-ball preimages of the vertex embedding
  are finite (finite-window properness).
- `planeDual_sphericalWindow`: for any connected labelled base cycle `G`, the
  same two-branch window on `lengthTwoTheta G.Edge` has the accepted exact
  bundled `GraphicDualCertificate` as well as the spherical circuit.
- `selectedConfig_ne_allOpen_of_ne`: a third distinct branch, with either
  Boolean orientation, witnesses that the selected configuration is not
  all-open.

## Fully explicit non-all-open example

`ConcreteTriangle.triangleGraph` is obtained by subdividing one edge of the
accepted two-edge cycle. It has three edges and three vertices.
`isLabelledCycle_triangleGraph` transports both connectivity and the
open-forest condition through the actual subdivision operation; it does not
postulate a new matroid or embedding certificate.

The explicit branch indices are `some false`, `some true`, and `none`.
`ConcreteTriangle.planeDual_sphericalWindow` proves, on one and the same
realization and configuration:

1. the exact `GraphicDualCertificate` of `lengthTwoThetaPair triangleGraph`;
2. preconnectedness of the underlying theta simple graph;
3. that the two-outer-branch configuration is not all-open;
4. the actual spherical circuit of those two open outer branches.

`ConcreteTriangle.inner_closed` separately identifies every inner-branch label
as closed. Thus this is not a disconnected or all-open example.

## Residuals (not inferred)

- This is finite-window geometry. Varying `a` changes the realization, so the
  arbitrary-scale statement is **not** `HasOpenCircuitExhaustion` of one fixed
  infinite graph and is not advertised as cofinality.
- The exact bundled plane-dual certificate and the spherical circuit coexist,
  but this module does not identify the circuit with the entire vertex cut of a
  chosen dual-open component and does not derive it from dual nonpercolation.
- The proof establishes the `SphericalOpenCircuit` interface and actual metric
  crossings. It does not prove pairwise arc-disjointness, injectivity of a
  closed Jordan parametrization, or a Jordan theorem for arbitrary continuous
  embeddings.
- No FK probability comparison, infinite-cluster statement, `GlobalAtMostOne`,
  DLR uniqueness, or Theorem 1.11 conclusion is inferred.

## Source comparison (separate from proof status)

The primary HTML in `.scratch/source-review/paper-v1.html` was checked
locally. Theorem 1.11 concerns an infinite graph embedded in `R^2`, a locally
finite dual, and strong uniqueness in a parameter regime. Section 5.2 defines
plane graphs using nonintersection of edges except at common endpoints and
then uses a dual measure with no infinite cluster. The present declarations
only provide exact finite combinatorial plane duality and explicit finite path
geometry. They do not supply the source theorem's infinite plane realization,
arc-disjointness proof, stochastic dual nonpercolation, parameter interval, or
uniqueness assertion. No source-result completion is claimed.

## Verification

From `results/fk-qcritical`, using the already installed Lean 4.35.0 binary
directory prepended to `PATH`, the exact command was:

```sh
lake env lean /workspace/nucleus/work/projects/p-a57b611ad60a4cbc99162d56e011665d/repo/.ultramath/smwsz39k5/m3/GeneralizedThetaWindow.lean
```

The complete output is in `check.log`. Elaboration succeeds with default
heartbeats; only nonfatal style/linter warnings remain. `validation.log` scans
nine principal `#print axioms` results and records PASS: every one is exactly
`[propext, Classical.choice, Quot.sound]`. The scan also checks for no
`sorry`/`admit`/`unsafe`, axiom or opaque declarations, `sorryAx`, or heartbeat
override. The repository-wide `check.sh` was not run because this task does not
modify shared source/build/audit artifacts. No shared source, GitHub state, or
toolchain file was changed. A concurrent `Audit.lean` modification and
`FK/IndexedSleeveInfinite.lean`/documentation files shown by final `git status`
belong to other work and were not touched by this direction.
