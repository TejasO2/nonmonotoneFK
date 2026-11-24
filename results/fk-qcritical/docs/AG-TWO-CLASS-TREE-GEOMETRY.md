Public modules (after integration): `FK.AGTree.{Aut,Transitive,Degree,EdgeClass,Spine,Devices,Invariant}`.
Only module prefixes/imports would change during integration; the declarations
below are the ten principal ones plus their support lemmas.  The development is
Lean 4.35.0 against the repository's pinned Mathlib, default heartbeats, no
`sorry`/`admit`/custom axiom/`unsafe`/`native_decide`, and the axiom audit
reports only `propext`, `Classical.choice`, `Quot.sound`.

# Direction 5 — quasi-transitive bounded-degree geometry for the two-class tree

Swarm `smwu4rrf3`, member `m7`.  Source: `.ultramath/smwu4rrf3/m7/Ultra/`.

## Result

`FK/AGTree/` previously built an explicit five-regular reduced-word tree
(`Ultra.G`, alphabet `Sum (Fin 3) (Fin 2)`), its two-rate independent bond law
`law r`, base nonpercolation below `1/2`, and a positive activated cluster at
`(3/10, 1/2)`.  `docs/AG-TWO-CLASS-TREE.md` recorded three explicit residuals
for that construction: base nonpercolation (since proved in
`FK/AGTree/BaseNonpercolation.lean` and `SharpThreshold.lean`), the exact
two-type critical value, and **quasi-transitivity**.  This development closes
the quasi-transitivity residual and the associated homogeneity, and supplies the
explicit double ray and separated star devices that the enhancement packing
interface needs:

* `Ultra.orbit_subsingleton` — the full automorphism group `G ≃g G` acts with
  **one** vertex orbit on the tree (not merely finitely many);
* `Ultra.isQuasiTransitive : FK.QuasiTransitive.IsQuasiTransitive Ultra.G`;
* `Ultra.degree_eq_five : ∀ v, Ultra.G.degree v = 5`;
* `Ultra.letterOf_mapEdgeSet_lmulListIso` — every word automorphism preserves
  the letter `letterOf` of every edge, hence the base/activation class and the
  two-rate `edgeRate`; the *labelled* reference model is homogeneous, not just
  the unlabelled tree;
* `Ultra.doubleRay : FK.EssentialEnhancement.DoubleRay Ultra.G` and
  `Ultra.onDoubleRay_rootEdge` — an explicit alternating spine;
* `Ultra.exists_separated_star_devices` — an instantiation of the repository's
  `FK.QuasiTransitive.exists_separated_star_devices` on this concrete graph:
  bounded-distance dense pivots on the double ray with pairwise separated star
  supports of at most five edges;
* `Ultra.law_map_perm_lmulListIso` — the product law `law r` is invariant under
  the induced coordinate permutation;
* `Ultra.measurableSet_infiniteClusterAt` and
  `Ultra.pr_infiniteClusterAt_eq_root` — the infinite-cluster event is
  measurable at every vertex and its probability does not depend on the vertex.

## Proof outline

**Automorphisms.**  In group language `Ultra.G` is the Cayley graph of the free
product of five copies of `Z/2`; left multiplication by a generator is a graph
automorphism.  At the word level the generator action is prepend-with-
cancellation,

```lean
def lpre (a : A) : List A → List A
  | [] => [a]
  | b :: t => if b = a then t else a :: b :: t
```

`lpre` preserves reducedness (`lpre_reduced`), is an involution on reduced words
(`lpre_lpre`), and commutes with appending a letter away from the empty word
(`lpre_append_singleton`).  Hence `lmul a` is an involution of `V` and satisfies
`G.Adj (lmul a v) (lmul a w) ↔ G.Adj v w` (`lmul_adj_iff`); the resulting
`lmulIso a : G ≃g G` is the single-letter automorphism.  The only non-formal
point in `lmul_adj` is the root: at `v = root` the edge `{[], [a]}` is reversed
onto itself by cancellation, which is handled by the two explicit list cases;
`lpre_append_singleton` covers every other edge.

**Transitivity.**  Iterating letters, `lmulList l` is left multiplication by the
word `l`, and `lmulListIso l root = ⟨l, ·⟩` for every reduced `l`
(`lmulListIso_root`).  Composing with an inverse automorphism gives
`vertex_transitive v w : ∃ φ : G ≃g G, φ v = w`, and the orbit quotient is a
subsingleton.  `isQuasiTransitive` is then `Finite.of_subsingleton`.

**Regularity.**  Vertex transitivity reduces `degree` to the root, where the five
appended letters give an explicit bijection `A ≃ G.neighborSet root`
(`rootNbr`); with `SimpleGraph.card_neighborSet_eq_degree` this gives
`G.degree root = 5` and hence `G.degree v = 5` everywhere.

**Class preservation.**  Writing an edge as a child pointer
`childE ⟨(u, c), h⟩` with letter `c` (the bijection `childE` of
`FK/AGTree/Edges.lean`), one shows by cases on `u.w` that
`lmulIso a` maps it to a child pointer of the same letter `c`
(`mapEdgeSet_childE`).  The two exceptional configurations are: the root's own
`a`-edge, which is reversed onto itself, and the root's `c`-edge for `c ≠ a`,
which is extended to `{a, [a, c]}`.  Off the root `lmul_snoc_of_ne_nil` gives
the list identity `a·(u ++ [c]) = (a·u) ++ [c]`.  Injectivity of `childE` then
yields `letterOf (φ.mapEdgeSet e) = letterOf e`, inductively for word
automorphisms.

**Double ray.**  Alternating words `altWord x y n` (letters `x y x y …`, built
as `(List.range n).map (altNext x y)`) are reduced (`altWord_reduced`), and the
bi-infinite spine sends `n ≥ 0` to the `x`-starting alternating word of length
`n` and `n < 0` to the `y`-starting alternating word of length `-n`.  Consecutive
spine vertices are adjacent by `altWord_succ` (the right ray) and by the prefix
relation (the left ray); distinctness uses the length `n.natAbs` and the first
letter.  Taking `x = Sum.inl 0`, `y = Sum.inl 1` gives `doubleRay` and the
root's own class-0 edge as a pivot on it.

**Devices.**  `FK.QuasiTransitive.exists_separated_star_devices` needs exactly
`G.Connected`, `IsQuasiTransitive G`, `[G.LocallyFinite]` and an `OnDoubleRay`
edge incident to a chosen vertex; the star supports are the actual incidence
stars, and `card_starDevice` with `degree_eq_five` gives the uniform size bound
`5`.

**Invariance.**  `law r` is `Measure.infinitePi` of the per-edge Bernoulli
measures `bernoulliMeasure true false (r (acls (letterOf e)))`.  Class
preservation makes `(μ ∘ φ.mapEdgeSet) = μ`, and
`Measure.infinitePi_map_piCongrLeft` gives
`(law r).map (piCongrLeft _ φ.mapEdgeSet) = law r`.  Transporting open
adjacency, connectivity and clusters along `φ` gives
`clusterSet (permConfig φ ω) (φ v) = φ '' clusterSet ω v` and hence
`InfiniteClusterAt (permConfig φ ω) (φ v) ↔ InfiniteClusterAt ω v`.  The root
event is measurable as `⋂ n {Fwd ω root n}` (`measurableSet_fwd`,
`cluster_eq_iInter`), and the vertex-`v` event is the image of the root event
under a measurable equivalence, hence measurable; `Measure.map_apply` then gives
`pr r {InfiniteClusterAt · v} = pr r {InfiniteClusterAt · root}`.

## Scope and residuals (honest)

* Not proved: an `hAG` instance, the exact two-type critical value, a
  critical-window/reference-shift theorem, or any DLR statement.  The only
  threshold facts appearing in `two_class_reference_model` are the repository's
  already-proved `base_nonpercolation` and `activated_percolation` on the same
  graph; they are not reproved and not improved here.
* The tree has no cycles; `FK.QuasiTransitive.exists_separated_cycle_devices`
  is therefore vacuous on this graph (its `c₀.IsCycle` hypothesis is
  unsatisfiable).  Acyclicity of `Ultra.G` is not formalized in this
  development, so the vacuity is a mathematical remark, not a Lean theorem.
* `pr_infiniteClusterAt_eq_root` is a per-vertex probability equality (a
  homogeneity statement), not a rate-monotonicity or shift statement.
* The measure-invariance statement is stated for the coordinate permutation
  `MeasurableEquiv.piCongrLeft _ φ.mapEdgeSet`; the identification with the
  configuration-level map `permConfig φ` is `Ultra.permCongr_eq_permConfig`.

## What "matches the BoundedRange class" means here

The library does not contain a named Lean class for the AG bounded-range
reference model; the relevant interfaces are
`FKLimit.IsSeparatedDeviceFamily`, `FK.Theorem14.BoundedDistance`,
`FK.EssentialEnhancement.OnDoubleRay` (used here) and
`FK.AGImplant.deviceConfig` (the shared-activation device model of
`FK/AGBoundedRangeImplant.lean`, *not* used here).  Accordingly:

* the reference law is the coordinate-wise independent two-class product `law r`
  with radius-0 dependency and rate class invariant under the automorphism group
  (`edgeRate_mapEdgeSet_lmulListIso`, `law_map_perm`);
* the enhancement devices are the actual incidence stars (support at most five),
  packed with `IsSeparatedDeviceFamily` and `BoundedDistance`
  (`exists_separated_star_devices`);
* the graph is connected, locally finite, quasi-transitive and regular of degree
  five, with an explicit double ray.

There is no shared global activation and no unbounded-degree or `pc = 1`
device in this construction.

## Integration notes

* New files map to `FK/AGTree/Aut.lean`, `FK/AGTree/Transitive.lean`,
  `FK/AGTree/Degree.lean`, `FK/AGTree/EdgeClass.lean`, `FK/AGTree/Spine.lean`,
  `FK/AGTree/Devices.lean`, `FK/AGTree/Invariant.lean`, `FK/AGTree/Audit.lean`
  (the last one for the audit only, not for `FK.lean`'s imports).
* Import lines `Ultra.X` become `FK.AGTree.X`; the namespace stays `Ultra`, and
  no added name clashes with an existing `FK/AGTree/*` declaration (checked for
  `lpre`, `lmul`, `lmulIso`, `lmulList`, `lmulListIso`, `altWord`, `altNext`,
  `spine`, `spineA`, `spineB`, `doubleRay`, `rootPivot`, `rootNbr`,
  `permConfig`, `isQuasiTransitive`, `degree_eq_five`, `letterOf_mapEdgeSet*`,
  `law_map_perm*`).
* Suggested `docs/PROOF-STATUS.md` wording for the AGTree row: replace
  "Quasi-transitivity, `hAG`, an exact two-rate critical value, critical-at-half
  and DLR conclusions remain unproved" by "The tree is vertex transitive (one
  orbit) and regular of degree five, its word automorphisms preserve the edge
  classes, and it carries an explicit double ray and separated star devices of
  size at most five (`FK/AGTree/{Aut,Transitive,Degree,EdgeClass,Spine,Devices}.lean`);
  the two-rate law is invariant under the automorphisms and the
  infinite-cluster probability is the same at every vertex.  `hAG`, an exact
  two-rate critical value, critical-at-half and DLR conclusions remain
  unproved."
