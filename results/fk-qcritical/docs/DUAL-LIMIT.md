# Conditional duality through FK weak limits

Public module: `FK.DualLimit` (namespace `FK.InfiniteVolume`). It extends the
finite equation (12) of `FK.DualParameterDuality` to external-boundary
conditional-law limits and the corresponding uniqueness reductions. It is not
an unconditional Theorem 1.11 or a proof of dualizability for every boundary
schedule.

## Exterior configurations and complements

`map_conditionalLaw_cfgDual_dualParameter` upgrades a boxwise PMF identity at
the actual `dualParameter` to conditional measures with arbitrary exterior
configurations. `extDual_invol` exchanges the required primal and dual
conventions, and the dual kernel identity transports the normalized FK law.

`openExterior` is the all-open exterior of a box, and
`map_finiteVolumeLaw_cfgDual_dualParameter` makes a necessary bookkeeping
point: complementing a primal closed-exterior `finiteVolumeLaw` produces a dual
conditional law at the all-open exterior, **not** another closed-exterior law.
Calling the result an `IsFKLimit` requires converting back through the already
proved conditional/finite-volume cylinder equivalence.

## Limits and dual uniqueness

`cyl_preimage_cfgDual` identifies the complement of a finite-coordinate
cylinder with the cylinder of the complemented pattern. Then
`tendsto_conditionalLaw_cfgDual` transfers weak convergence from primal
external-boundary conditional laws to the dual laws at complemented exteriors.

The `dualExhaustion` has unchanged global edge labels, hence is again a valid
box exhaustion. `isFKLimit_map_cfgDual` converts the preceding conditional-limit
statement back into an FK-limit statement at the dual parameter. Since global
complementation is involutive, `eq_map_of_unique_dual_fkLimit` identifies every
dualizable primal FK limit as the complement of the unique dual FK limit.

`theorem_1_11_modulo_dual_uniqueness` and
`theorem_1_11_modulo_dual_family_uniqueness` then use the existing tail
Choquet/limit-class theorem to identify all members of the total primal FK
family. These are genuine measure-theoretic reductions, but their
`hdualizable` argument requires duality for **every** primal boundary sequence,
not just one free convention. That is still a geometric and convention-
independence obligation.

`map_conditionalLaw_planeBox_cfgDual` discharges the finite identity in the
actual plane-box model from `planeBox_pmf_dualParameter`; its Euler component
relation remains an explicit hypothesis. The all-box DLR transport and
identification avoid replacing global dual uniqueness with the stronger and
inconvenient one-box singleton condition. `eq_map_of_unique_dual_generalExterior`
covers the typical-exterior form produced by the previously proved Proposition
1.8(1) weak-limit representation.

Finally, `max_dualParameter_prime_eq_one_sub_min` gives
$\max(p^*,p'^*)=1-\min(p,p')$ at the actual normalized dual parameter, and
`parameter_window_iff_dualParameter` converts the subcritical parameter
window without confusing it with the real-valued `FK.dual` presentation.

## Remaining obligations

The proof does not produce the plane embedding/Euler certificates, infer that
arbitrary boundary schedules admit (12), prove dual strong uniqueness, derive
at-most-one/infinite-cluster geometry, or assemble essential enhancements on
primal and dual graphs. The second half of Theorem 1.11 also needs existence
of an infinite cluster from the independent supercritical reference argument.
The measure bridge substantially narrows the infinite-volume step, but does not
hide or discharge those inputs.

The exact source was independently rebuilt with pinned Lean 4.35.0 and default
heartbeats. All 13 principal axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.
