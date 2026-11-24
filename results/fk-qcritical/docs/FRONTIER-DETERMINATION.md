# Free fibres and frontier-mass determination

Public modules: `FK.FreeFibre` and `FK.RegionFrontierDetermination`
(namespace `FK.M3`). These provide a precise deterministic criterion for
uniqueness; they do not construct the shared frontier masses or a random
tower identity.

## Free conditional law on the fibre

`real_apply_eq_freeMass_of_partition_bot` applies the actual DLR equation:
integrating the conditional FK law at the observed exterior gives the
unconditional event mass. If the induced partition is discrete almost surely,
the constituent conditional mass is the actual free normalized FK mass,
for every measurable finitely supported event inside the box, not only the
usual cylinder basis. A countable common null set identifies it with the
closed-exterior reference value.

The `region_stratum_rect` refinement then treats finite attained random
regions. The mass of a stratum is the frontier-restricted exterior marginal
times the induced free interior law cut to the event that a base is connected
inside the region. Arbitrary interior-supported events have the analogous
interior readout identity after the forced-connectivity restriction.
Merely applying this to a DLR class does not pretend the induced connection
set is the entire interior: it is the relevant random closed region.

## Covering countable strata and determining the law

The almost-surely finite regions cover every configuration except a null
event, and attained-region strata are pairwise disjoint. Therefore any
measurable event is the sum of its intersections with those strata. Optimize
the support to a finite vertex base containing all endpoints of the wanted
event and use `regionBoxOf` to read the supporting edges as interior edges.
The result is a formula where only the decreasing frontier-closed mass is
law-dependent; the induced normalized FK factor is otherwise fixed.

`eq_of_forall_frontier_mass_eq` hence proves that if two laws satisfy the
actual region-box DLR equations, each assigned region is a.s. finite, and
for every finite region their exterior masses on the closed-frontier event
coincide, then the two probability measures coincide.

This is a strong and correctly delimited reduction, but it needs **equality**
of that entire decreasing mass family. A common dominating law produces
inequalities on open connections, not equal frontier probabilities, and an
arbitrary ordered coupling or conditional independence does not discharge
this numerical input. Nor does this imply the random-tower property at a
varying σ-field. The remaining paper proof must construct genuine adaptive
regions, measurable varying filtrations and joint martingale comparison, or
show this equality directly. No unconditional Theorem 5.1, 1.9 or 1.10 is
asserted.

The exact files were rebuilt independently at default heartbeats; all 6
principal axiom reports (one repeated audit line is omitted from their count)
contain only `propext`, `Classical.choice` and `Quot.sound`.
