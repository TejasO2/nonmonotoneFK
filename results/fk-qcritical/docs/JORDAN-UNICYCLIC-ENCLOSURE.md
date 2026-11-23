# Scoped Jordan outer circuits and an explicit fixed exhaustion

## Artifact and verification

`JordanUnicyclicEnclosure.lean` imports only public `FK.*` modules and compiles
with the pinned Lean 4.35 environment and default heartbeats:

```bash
cd results/fk-qcritical
. ../../.scratch/elan/env
lake env lean ../../.ultramath/smwswa9cs/m2/JordanUnicyclicEnclosure.lean
```

`audit-output.txt` is the captured final run. All 25 principal `#print axioms`
checks report exactly a subset of `propext`, `Classical.choice`, and
`Quot.sound`. There are no `sorry`, `admit`, `unsafe`, new axioms, heartbeat
overrides, toolchain changes, or shared-result writes.

## Exact combinatorial outer-boundary result

For an arbitrary `UniqueCycleCertificate G`, bridge-face assignment, and
configuration `ω`, let `S` be the inside face's actual component in the
complementary configuration of `unicyclicDualPair G hG bridgeFace`. If the
exterior face is outside `S`, then:

* `vertexCut_insideComponent` proves the **whole** dual vertex cut of `S` is
  `hG.cycleEdges`; bridge labels are dual loops and cannot occur in the cut.
* `isCircuit_cycleEdges` and `eq_cycleEdges_of_isCircuit` prove that the
  distinguished cycle is the unique primal matroid circuit.
* `cycleEdges_open` proves every cycle label is open in `ω`, and
  `reachable_on_cycleEdges` proves its carrier is connected using only its
  own open labels.
* `sphericalOpenCircuit_insideComponent` combines that exact cut with supplied
  arc/radius data to produce an actual `SphericalOpenCircuit`. The arc input
  concerns only the unique cycle; no arbitrary matroid circuit is postulated
  to be Jordan.

The finite theorem does not assume an all-open primal graph or a preselected
boundary circuit. Exterior-face exclusion is the explicit finite geometric
scope.

## Concrete polygonal digon

`PolygonDigon` uses the exact two-face dual of `twoEdgeCycle`. Its two labelled
arcs travel along the upper and lower three sides of a square in the sup-norm
plane `ℝ × ℝ`.

* `upperArc_dist_eq` and `lowerArc_dist_eq` prove that every point of either
  arc has distance **exactly** the outer scale from the origin. The lower bound
  uses a fixed coordinate on each constituent segment; the upper bound is
  convexity of distance.
* At outer scale `4*r`, `labelledArc_off_sphere` and
  `embeddedVertex_off_sphere` prove avoidance of the radius-`r` sphere.
* `graphicDualCertificate` is the integrated exact certificate, not a new
  hypothesis. `exterior_not_mem_inside_allOpen` computes the all-open dual
  inside component from its all-closed connection graph.
* `sphericalOpenCircuit_allOpen` and `exists_sphericalOpenCircuit_gt` give the
  actual finite spherical circuit and radii cofinal in `ρ`. The latter varies
  the realization scale and is explicitly not an exhaustion of one fixed
  realization.
* `edgeCut_insideComponent_eq_univ` computes the concrete simple-graph
  `DualExhaustion.edgeCut`; `simpleLabels_cycle_eq_edgeCut` identifies it
  exactly with the selected face-dual cycle's simple-label image.

## Actual fixed infinite-graph exhaustion

`PolygonDigon.ScaledFamily` constructs one fixed simple graph on
`ℕ × twoEdgeCycle.Vertex`, with disjoint digon-quotient components. Component
`n` has scale `4*(n+1)`. The fixed realization uses its upper polygonal arc and
the all-open global configuration.

* `dist_realization_arc` proves every global arc lies exactly on its source
  component's outer sphere.
* Selected radii are `n + 1/2`, not integers. `scale_ne_radius` proves by
  parity that `4*(m+1) ≠ n+1/2` for all natural `m,n`.
* `localEmbedding` is an actual endpoint-preserving labelled/simple embedding
  using the graph-homomorphism edge map. `crossing` proves that no global arc
  meets the selected sphere; `vertex_off` proves the analogous vertex fact.
* `sphericalOpenCircuit` supplies the selected globalized unique cycle through
  the integrated compatibility theorem.
* `hasOpenCircuitExhaustion` proves the genuine fixed-realization
  `HasOpenCircuitExhaustion` at every real lower bound `ρ`.
* `finite_vertex_preimage_ball` bounds component indices by `⌈r⌉₊` and each
  fibre by two vertices. `globalAtMostOne` then applies the integrated
  open-circuit uniqueness theorem to this exact configuration.

## Subsequent exact criterion

`ConnectedUnicyclicWindow` proves equivalence between openness of the unique
cycle, exclusion of the exterior face, and equality of the full inside vertex
cut with that cycle, while allowing arbitrary bridge states. A connected
core-open/pendant-closed example supplies the same spherical geometry with a
west-centred enclosure and an outside leaf. These remain rescaled finite
windows, not the global Jordan result below.

## Explicit residuals and non-claims

1. The fixed infinite example is deliberately **disconnected and all-open**.
   Its components are finite; its `GlobalAtMostOne` conclusion is not evidence
   for a general connected graph or a stochastic FK theorem.
2. This artifact does not derive the generic exterior-face exclusion from
   `DualFiniteEnclosure` or from global dual nonpercolation. It does not build
   the required global plane-dual pair for the scaled family.
3. The concrete digon identifies its labelled component boundary with the
   actual `DualExhaustion.edgeCut`. The missing bridge from **arbitrary metric**
   `DualFiniteEnclosure.edgeCut`s to suitable component boundaries, and
   subsequent global plane-dual transport, remains open.
4. Generic unicyclic spherical geometry still requires its explicitly stated
   path, vertex-off-sphere, and crossing inputs. Only the concrete polygonal
   digon discharges them here.
5. No arbitrary continuous plane embedding, general Jordan outer-boundary
   theorem, full Theorem 1.11, or dual-nonpercolation implication is claimed.
