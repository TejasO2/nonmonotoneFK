# Boundary-wiring monotonicity and the free/wired sandwich

Public module: `FK.GibbsOrder`. For a finite labelled multigraph with arbitrary
boundary setoid and $1≤q$, $0<p<1$, coarsening the boundary setoid moves the
normalized FK law upward in stochastic order.

The new `componentCount_diff_antitone` uses coranks in $\mathbb F_2$. The
vectors for newly opened labelled edges are the same for the finer and coarser
wiring, so rank diminishing returns gives the needed row/column comparison.
`componentCount_wiring_mlr` follows, then the standard Holley inequality yields
`fkPMF_expectation_mono_wiring` and `fkMeasure_mono_wiring`. Loops, parallel
labels and arbitrary vertex setoids are retained.

`fkMeasure_sandwich` gives the free-vs-wired finite comparison.
`finiteVolumeLaw_sandwich` and `fkLimit_sandwich` carry it to the actual box
model and to supplied free/wired weak limits. The free/wired names here are the
discrete and universal finite boundary conditions, not the free and
wired-at-infinity conventions of §1.3.

The upper-corner pattern lattice supports the remaining separately useful step:
`cylinder_eq_of_upT_eq` recovers the mass of every finite-coordinate cylinder
from upper-corner masses, and mutual domination therefore gives all cylinder
masses. If free and wired schedules have the same limit, every FK weak limit has
those masses too.

## Not proved here

This does not construct the canonical free/wired limits, establish the full
strong-uniqueness equivalence, or apply to $q<1$. Equal cylinder mass is not yet
the final π–λ theorem equality of probability measures, and no Gibbs
at-most-one-cluster or Burton–Keane property is inferred. Those are genuine
remaining inputs, not hypotheses hidden in the weak-limit statements.

The twelve principal axiom reports use only the standard foundational axioms.
The source was independently rebuilt under the pinned Lean 4.35 with no compiler
warnings.
