# Direction F: nested-boundary DLR uniqueness assembly

## Result

`NestedBoundaryUniqueness.lean` adds a quantitative DLR/tail assembly theorem,
rather than another direct finite-volume weak-limit comparison.

* `HasVanishingExteriorCouplingError exh Φ hq hp μ ν` is a common auxiliary
  representation of `μ` and `ν` with an error `err n z → 0` a.e. and an
  eventual bound on the absolute difference of their **actual**
  `FiniteBox.conditionalLaw` probabilities of every finite-base cylinder.
* `eq_of_extremal_dlr_of_hasVanishingExteriorCouplingError` proves `μ = ν` for
  two extremal members of the same exact DLR class. The proof transports the
  existing full-sequence a.e. reverse-martingale limits to the common space,
  applies the squeeze theorem to the coupled difference, and then uses
  extensionality on Boolean cylinders. Tail triviality comes from extremality;
  it is not an extra hypothesis.
* `eq_dlr_of_pairwise_hasVanishingExteriorCouplingError` proves equality of
  arbitrary DLR laws if every pair of extremal DLR laws has the above coupling.
  It selects a genuine extremal DLR tail fibre as reference and applies the
  completed `eq_dlr_of_extremal_unique` Choquet theorem to both laws.

The boundary assignment `Φ` is explicit and arbitrary. Nothing in the module
identifies the right-wired free-left/right-supported split class with that
arbitrary-boundary DLR class.

## Remaining mathematical input

This is conditional DLR uniqueness, not full Lemma 2.1/Theorem 1.9. For a
specific nested-box geometry `NestedFiniteCoupling` now constructs the common
auxiliary space and exact second restriction internally. Its conditional
estimate still requires the common free-interior law on **genuine global**
maximal closed-cutset strata. One must also instantiate the intended nested
geometry and establish the finite conditional-cylinder bound with an
a.e.-vanishing error for every extremal pair. Those stochastic/geometric steps,
not a separate second-marginal identity, are the remaining finite blockers.

## Verification

Compiled independently with repository Elan `.scratch/elan`, Lean `4.35.0`,
its project `LEAN_PATH`, and default heartbeats:

```bash
bash compile.sh
bash compile.sh NestedBoundaryAudit
```

Outputs and logs are under `.scratch/oleans` and `.scratch/logs`. The audit
prints only `[propext, Classical.choice, Quot.sound]` for all four public
declarations. A scan of the member's Lean files finds no `sorry`, `admit`,
`unsafe`, or new `axiom`. No shared-results file or Git remote was modified.
