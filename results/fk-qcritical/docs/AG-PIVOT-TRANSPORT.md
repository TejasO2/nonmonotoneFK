# Bounded-local probability transport for AG peeling

## Scope

`AGPivotTransport.lean` is a proposed module; no shared source was edited. It uses the repository Elan/Lean 4.35 environment and imports the existing `FK.AGPeeling` and `FK.OpenPathEnhancement` modules.

This closes the finite change-of-variables and source-fibre component of the Aizenman–Grimmett pivot argument. It does **not** prove the strict critical-point shift, the global expected-pivot-count comparison, or the combinatorial bounded-radius enhancement gadget.

## Main declarations

All declarations are in `FK.AGPeeling`.

### General finite transport

* `event_mul_le_of_bounded_fibres`: for a finite probability law, a deterministic map `T`, a pointwise one-sided mass ratio `c`, and a bound `k` on source fibres, proves
  `c * μ.event S ≤ k * μ.event B` whenever `T '' S ⊆ B`. Injectivity is not required.
* `FinProb_mass_le_one` and `FinProb_event_split` are the finite-probability support lemmas.

### Automatic local support and product ratio

* `IsLocalModification R T` says precisely that `T ω` and `ω` agree outside `R`.
* `ncard_local_fibre_le`: every source fibre of an `R`-local Bool modification has cardinality at most `2 ^ R.card`. The proof injects a fibre into functions `R → Bool`.
* `pi_mass_pow_mul_le_of_local`: for arbitrary independent finite Bool coordinate laws `ν`, if `δ` is a common lower bound for both coordinate masses, then configurations agreeing outside `R` satisfy the exact one-sided comparison
  `δ ^ R.card * (FinProb.pi ν).mass ω ≤ (FinProb.pi ν).mass η`.
* `local_pi_event_mul_le`: combines the preceding results. No separate fibre or likelihood-ratio hypothesis remains.
* `local_joint_edgePivotal_event_mul_le`: the direct separate-bond/separate-activation `JointConfig` corollary, retaining `Sum.inl`/`Sum.inr` coordinates and independent finite probability normalization.
* `closeList_isLocalModification` and `closeActivations_isLocalModification`: the existing peeling maps have exactly the listed-coordinate supports.

### Actual peeling branches

* `HasActivationPeelWitness` packages the first branch of the existing `peel_activations`.
* `activationPeelTarget` canonically chooses that branch's target and is the identity off the branch. `activationPeelTarget_spec` and `activationPeelTarget_isLocalModification` prove its required properties.
* `activationPeel_branch_event_mul_le`: transports the source with an actual activation-peeling witness. No proposed-map validity hypothesis remains: `activationPeelTarget_spec` supplies it.
* `closeActivations_branch_event_mul_le`: on the complementary source, the existing `peel_activations` supplies event membership and the retained bond pivot after closing all candidates. Only the genuine increasing-event hypothesis `hA : IsUpperSet A` is needed.
* `peel_activations_event_mul_le_sum`: partitions the full source event and sums the two inequalities.

For the last theorem, put
`R = (l.map Sum.inr).toFinset`, `μ = FinProb.pi (Sum.elim bond activation)`, and `K = 2 ^ R.card`. It proves

    δ ^ R.card * μ.event {ω | ω ∈ A ∧ EdgePivotal A e ω} ≤
      K * μ.event {η | η ∈ A ∧ EdgePivotal A e η ∧
        ∃ z ∈ l, ActivationPivotal A z η} +
      K * μ.event {η | η ∈ A ∧ EdgePivotal A e η}.

Overlap of the two targets is intentional; the conclusion uses a sum, not a disjoint-union identity.

## Remaining inputs and work

* `E` and `F` are finite, as required for this finite-volume component. The coordinate laws remain independent and normalized by `FinProb`; bond and activation rates need not be homogeneous.
* A common `0 ≤ δ` lower bound for both values of every coordinate remains. Choosing `0 < δ` is needed for a nonvacuous comparison and excludes zero coordinate masses. No arbitrary `g(p,s)` is assumed.
* For the peeling dichotomy, `A` must be increasing. The candidate list `l` and its exact support `R` remain. A metric bounded-radius ball can be used as `R`, but this module does not construct graph balls or prove a radius bound for a gadget.
* The second target is only the activation-free peeling conclusion: membership in `A` and the same bond pivot. Converting that branch into an activation-pivot target is the remaining local enhancement-gadget work.
* Summing over pivot locations to obtain `E Ns ≥ g E Np`, applying Margulis–Russo, and passing to infinite volume are not proved here.

## Verification

The module was compiled twice independently with the repository environment, including generation of `AGPivotTransport.olean` for the audit import. `AGPivotTransportAudit.lean` audits all 17 declarations. `AGPivotTransportAudit.txt` records only

    [propext, Classical.choice, Quot.sound]

for every declaration. A token scan found no `sorry`, `admit`, `unsafe`, or new `axiom` declaration in the module or audit file.
