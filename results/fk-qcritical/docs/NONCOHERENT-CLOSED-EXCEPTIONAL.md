# Closed-exception stabilization for varying coherent sources

## Stabilization criterion

For a constant source sequence,
`locallyStabilizes_const_iff_measure_closure_disagreement_eq_zero` identifies
joint local stabilization exactly with nullity of the **closure** of the
disagreement set. More generally,
`locallyStabilizes_of_eventually_eqOn_compl_closed` proves stabilization from
eventual agreement off one fixed closed null exceptional set. Terms need not
agree globally and local constancy is not assumed separately.

This is stronger than almost-everywhere agreement for a good reason. The compact
Boolean product example uses the all-true apex, a specification agreeing with
the constant specification only at that apex, and its Dirac point mass. The
disagreement set is null but its closure is everything: a sequence formed by
flipping one apex coordinate lies in disagreement and converges to the apex.
`ae_agreement_not_locallyStabilizes` therefore proves almost-everywhere agreement
together with failure of local stabilization. Dense probes alone cannot fill
the gap.

## Coherent DLR closure

Every source coherent convention supplies smaller-box DLR equations for its own
closed-exterior finite-volume laws via `eventually_isDLR_finiteVolumeLaw_coherent`.
Combining those equations with closed-exception eventual agreement proves
`mem_dlrMeasures_of_tendsto_coherent_of_eventually_eqOn_compl_closed`: a weak
limit of genuinely varying coherent finite-volume laws satisfies the target DLR
class, assuming the target's local regularity as displayed in the theorem.

The geometric variant derives that local regularity from exterior at-most-one
uniqueness. The `IsFKLimit` variant retains $0<p<1$, exact arbitrary-boundary
limit conventions, the actual graph/box data, and global at-most-one-cluster
uniqueness almost surely, invoking the established noncoherent finite-energy
bridge. The target need not itself be a coherent convention and no agreement
is needed on the exceptional sets.

These are conditional varying-coherent-source closures. They do not prove the
unrestricted fixed-source implication refuted by the one-edge
`NoncoherentCounterexample`, remove the exceptional-set hypotheses, establish
weak-limit existence, or extend the final interior `IsFKLimit` specialization to
arbitrary unrelated boundary sequences at other rates.

## Verification

The exact candidate was independently compiled with Lean 4.35.0 and default
heartbeats. Seventeen principal definitions/theorems were checked in a separate
expanded axiom audit. Reports use at most `propext`, `Classical.choice`, and
`Quot.sound` (several explicit finite definitions need none). The source has no
placeholder, unsafe/custom axiom, or elaboration override. The full release
script checks the public imports and all audits.
