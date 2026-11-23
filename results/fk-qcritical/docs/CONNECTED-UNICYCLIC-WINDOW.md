# Connected unicyclic outer-boundary windows

## Deliverable

`ConnectedUnicyclicWindow.lean` imports only the public module
`FK.JordanUnicyclicEnclosure`. It elaborates under the repository's existing
Lean 4.35.0 toolchain, with default heartbeats and no placeholder or custom
axiom declarations.

The general two-face results are for a labelled multigraph with a supplied
`UniqueCycleCertificate` and an *arbitrary* bridge-face assignment. In
particular, no all-open premise and no openness condition on bridges is used.
The principal declarations are:

- `exterior_not_mem_inside_of_cycleEdges_open`: openness of the unique primal
  cycle prevents the inside dual-open component from reaching the exterior
  face. The proof shows that every possible interior/exterior dual adjacency is
  either a closed cycle label or a non-cycle dual loop.
- `vertexCut_insideComponent_of_cycleEdges_open`: consequently the *entire*
  inside vertex cut is exactly the distinguished cycle.
- `cycleEdges_open_iff_exterior_not_mem` and
  `vertexCut_eq_cycleEdges_iff_exterior_not_mem`: the new exact converse
  formulations
  `cycle open ↔ exterior excluded ↔ full inside vertex cut = cycle`.
- `sphericalOpenCircuit_of_cycleEdges_open`: the cycle is an actual
  `SphericalOpenCircuit`, whose definition includes both openness and
  `OpenLabelConnected`, under explicit nonloop, vertex-off-sphere and
  crossing-control data.

The path-realization interface also constructs a simple-quotient realization
from an arbitrary labelled realization, with the selected arc always given by
an actual label (possibly reversed), preservation of arc-locus membership, and
exact transport of crossing control to `simpleLabels`.

## Connected non-all-open example

`ConnectedDigon.oneLeafDigon` is the two-edge digon with one genuinely attached
pendant label. Its underlying simple graph is connected (`preconnected`). The
configuration `coreOpenPendantClosed` opens both cycle labels and closes the
pendant. For arbitrary bridge-face assignments the example has the exact full
cycle cut. Explicit polygonal arcs in the sup-norm plane prove vertex avoidance,
arc avoidance/crossing control, and spherical circuits centred both at the
origin and at the west core vertex. The west-centred circuit strictly encloses
the west vertex (`west_mem_circuit_ball`), while the pendant leaf is outside
(`leaf_not_mem_west_circuit_ball`). `finite_vertex_preimage_ball` proves finite
preimages of every metric ball.

The unaccepted handoff was not trusted on the strength of its audit commands:
independent elaboration found and repaired two failures, at the west-centre
zero-distance non-equality and at the pendant-distance sphere contradiction.
The repaired geometric lemmas and their dependents recheck successfully.

## Scope and residuals

This is a finite connected-window theorem. The realization scale is `4*r`, so
quantifying over positive radii here is **not** an exhaustion of one fixed
infinite graph. Finite-ball properness follows from finiteness of this window;
it is not advertised as properness of an infinite embedding. The module does
not construct circuits from dual nonpercolation, prove a general Jordan
theorem for arbitrary continuous embeddings, or infer `GlobalAtMostOne`,
DLR/FK-measure uniqueness, or Theorem 1.11.

The remaining step toward an infinite connected result is to embed such exact
local two-face windows in one fixed connected locally finite graph, obtain
cofinal radii without changing the realization, and derive the required
exterior exclusion from the stochastic dual input.

## Source comparison (separate from proof status)

The primary HTML at `.scratch/source-review/paper-v1.html`, Theorem 1.11 and
§5.2, concerns an infinite plane graph and uses a dual law with no infinite
cluster to conclude at most one infinite primal cluster, followed by strong
uniqueness. The declarations here formalize only a finite two-face geometric
outer-boundary mechanism and an explicit mixed-state pendant example. They do
not supply the paper's dual law, its subcriticality/nonpercolation, its infinite
plane graph, or any parameter interval. No source-theorem completion is claimed.

## Verification

Base revision: `bc165faf5edd9ce57bd655f2ce23884c977b17b0`.

Command run from `results/fk-qcritical`, with the already-installed Lean 4.35
binary directory prepended to `PATH`:

```sh
lake env lean /workspace/nucleus/work/projects/p-a57b611ad60a4cbc99162d56e011665d/repo/.ultramath/smwsz39k5/m1/ConnectedUnicyclicWindow.lean
```

The complete output is retained in `check.log`. Every printed principal audit
is exactly a subset of `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx` occurs. A separate placeholder scan and an override scan are clean.
The repository-wide `check.sh` was not run: this task writes only in the member
directory and does not modify shared build/audit artifacts. No shared source,
GitHub state, dependency, or toolchain file was changed.
