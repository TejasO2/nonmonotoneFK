# Automorphism invariance, marked forests and the exactly-two case

The modules `FK.SourceAutomorphismInvariance` and `FK.ForestMarkedCount`
separate three different inputs in a Burton–Keane argument: model invariance,
configurationwise finite counting, and ergodicity. They do not by themselves
prove general Burton–Keane uniqueness, full cluster-count constancy, or
Theorem 1.11.

## Actual source-law invariance at $q=1$

`FK.BurtonKeane.Automorphism.eq_bernoulliConst_of_mem_sourceFKMeasures_q_one`
proves that every member of either summand of `SourceFKMeasures` at $q=1$ is
the constant Bernoulli product. Source weak limits use the exact `QOneLine`
weak-limit identification; all-region source-DLR laws are restricted along an
explicitly supplied vertex exhaustion. No automorphism invariance of the
boundary convention is needed.

Consequently `measurePreserving_permConfig_of_mem_sourceFKMeasures_q_one`
proves measure preservation under **every** graph automorphism. This is a
$q=1$ product-law theorem, not a general source-FK invariance theorem at
$q\ne1$.

The file also transports open walks, metric distances, three-way arms and
finite internal openings through automorphisms. `PatchedEncounterAt G y`
means that one finite vertex set has an internal opening after which the
centre $y$ has three-way arms at every scale. Existentially quantifying the
patch makes this a genuinely centre-local equivariant measurable event;
`homogeneousPatchedEncounterEvents` instantiates the existing
`Folner.HomogeneousEvents` interface only after an appropriate root-transitive
family of measure-preserving graph automorphisms is supplied.

`measure_threeInfiniteClusters_eq_zero_of_folner` then proves zero mass of
three separated infinite clusters from finite-pattern insertion tolerance,
actual automorphism invariance, and a **supplied configurationwise**
marked-count upper bound tending to zero relative to a sequence of nonempty
windows. A $q=1$ source-family wrapper supplies invariance and insertion
tolerance, but still retains the marked-count and root-transitivity inputs.
This theorem is explicitly conditional: no actual Følner sequence or
multi-centre forest is produced here.

## Multi-centre finite forest counting

`FK.BurtonKeane.TreeCounting` proves, for finite forests without isolated
vertices,
$\#\mathrm{branchpoints}+2\le\#\mathrm{leaves}$, allowing disconnected
components, paths and single-edge components. A boundary set containing all
leaves therefore bounds every branchpoint.

`markedCount_le_of_encounterForest` applies this to a possibly disconnected
configuration-dependent graph: if that graph is always acyclic with positive
degree, if every leaf belongs to the prescribed boundary, and if every marked
centre in a finite window has degree at least three, then the number of marked
centres is at most the boundary cardinality. It covers all marked centres in
one configuration, unlike the old fixed-tree bound. The required forest is a
hypothesis, not a construction; it supplies no general Følner theorem.

## Exactly two infinite clusters

`ExactlyTwoInfiniteClusters` means two separated infinite open clusters and
no third separated infinite cluster. The deterministic theorem
`exists_openInternal_globalAtMostOne_of_exactlyTwo` constructs one finite
connected internal opening that merges the two clusters. To prove no third
infinite cluster appears, finite-cluster-cover avoidance is used: every
post-patch infinite cluster descends to an infinite cluster of the original
configuration. Absence of a third original cluster puts it on one of the two
sides; the opened finite support joins the sides. This avoids assuming that
finite opening preserves cluster multiplicity.

Finite-pattern insertion tolerance and countable patch lifting therefore rule
out an almost-sure exactly-two phase in
`not_ae_exactlyTwoInfiniteClusters_of_insertionTolerant`. This argument needs
no invariance assumption and has a $q=1$ source-family specialization at
interior $p$.

`ExactlyTwoInfiniteClusters` is also measurable and exactly automorphism
invariant. Under the **additional explicit hypothesis**
`Ergodic (permConfig φ) μ`, its probability is zero or one. The preceding
insertion-tolerance contradiction rules out one, so
`measure_exactlyTwoInfiniteClusters_eq_zero_of_ergodic` gives zero mass.
A $q=1$ source wrapper is included. No particular graph shift is proved
ergodic, and this theorem does not replace the separate three-cluster/Følner
argument.

## Remaining obligations

- Construct the configuration-dependent multi-centre forest and an actual
  Følner sequence with sublinear boundary.
- Prove full infinite-cluster-count constancy and the corresponding
  zero/one/infinity theorem; exactly two is only one finite stratum.
- Supply actual ergodic shifts for intended applications and source-FK
  invariance at $q\ne1$ if needed.
- Assemble those inputs into a general at-most-one-cluster theorem and, only
  then, use that in a planar or phase-uniqueness argument.

Both sources were independently rebuilt sequentially using pinned Lean 4.35
and default heartbeats. All 20 audited declarations across the two modules
use only `propext`, `Classical.choice`, and `Quot.sound`.
