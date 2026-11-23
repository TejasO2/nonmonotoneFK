# Generalized length-two theta duality

## Result and coverage

`GeneralizedTheta.lean` defines `lengthTwoTheta ι`. Its vertices are two terminals
`Bool` plus one independent internal vertex for each `i : ι`; its two edges
`(i,false)` and `(i,true)` form the terminal-to-terminal path `branch i`.
Thus this is `K(2, |ι|)`, with every branch subdivided once. The number and the
finite type of branches are arbitrary, but **all paths have length two**; this is
not a claim about paths of arbitrary lengths.

For a connected labelled cycle `G`, `lengthTwoThetaPair G` pairs this primal
with `bundledGraph G`, which has the original cycle vertices and two parallel
copies of every cycle label. The only input is `G.IsLabelledCycle`, the existing
graph-theoretic cycle certificate. There is no input matroid-duality or general
planarity premise.

## Proof map

* `spanningTree_preconnected`, `spanningTree_ncard`, and `spanningTree_indep`
  construct the spanning trees and apply the project's actual component-count
  forest criterion.
* `not_indep_of_branch_pair` exhibits the remaining three-edge route after an
  edge is deleted from a pair of complete branches.
* `exists_spanningTree_superset` extends any set with at most one complete
  branch to one of those spanning trees. This proves
  `indep_iff_atMostOne_branch`, then `isBase_iff_spanningTree` and
  `isCircuit_iff_two_branches`. Circuits here are matroid circuits, not
  unsupported geometric Jordan-curve claims.
* `connectionGraph_bundledGraph` identifies the bundled connection graph with
  the base connection graph on projected support.
  `image_fst_diff_singleton_of_atMostOneCopy` and
  `isOpenForest_bundledGraph_iff` handle deletion of one parallel copy.
  Together with the labelled-cycle certificate, this proves
  `bundledGraph_indep_iff`: at most one copy per base label and proper support.
* `lengthTwoTheta_dual_cycleMatroid` compares independent sets directly. A set
  disjoint from a primal spanning tree has at most one copy in each bundle and
  misses the complete bundle. Conversely, these two conditions supply a disjoint
  spanning tree. No complementary-basis assertion is assumed.
* `bundledGraph_allOpen_preconnected` transports the base cycle's actual
  preconnectedness. `lengthTwoThetaPair_graphicDualCertificate` bundles the new
  matroid equality, nonempty faces, and this connectivity proof.

## Verification

Built using the repository Elan Lean 4.35 toolchain and the pinned project
`LEAN_PATH`, with no heartbeat setting:

```sh
LEAN_PATH="$BASE" lean -o GeneralizedTheta.olean GeneralizedTheta.lean
lean GeneralizedThetaAudit.lean
```

The second command used the member directory before `$BASE` in `LEAN_PATH`.
`GeneralizedTheta.audit.txt` records twelve independent `#print axioms` checks.
Every result contains only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders, unsafe declarations, or new axioms.
