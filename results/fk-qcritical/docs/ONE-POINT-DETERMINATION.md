# One-point determination for the finite random-cluster law

The public sources are `FK.OnePointDetermination` and `FK.FullSupportNecessary`, independently compiled and audited with Lean 4.35/default heartbeats. The normalized source law is the actual finite `G.fkPMF` over arbitrary finite labelled multigraphs and boundary setoids, not a heuristic PMF identity. The exact odds expression is cross-multiplied, so no nonzero denominator is implicitly assumed. These are finite results: no weak-limit or disintegration proof is imported by renaming them to DLR results.


Scope, exact statements, audit, and the precise residual for Proposition 1.8(2).

## Why this component

`docs/PROOF-STATUS.md` records that Proposition 1.8(2) is proved only as
coherent-closure plus convention transport, and that the remaining gap for an
*arbitrary* (noncoherent) `IsFKLimit` is the pair of explicit hypotheses
`hDLR` (induced local specifications and their smaller-box DLR equations) and
`hstab` (`LocallyStabilizes`) of

```
NoncoherentStabilization.mem_dlrMeasures_of_isFKLimit_of_locallyStabilizes_of_globalAtMostOne
```

The source's own route to `Φ`-Gibbs membership does not go through
stabilisation of a varying boundary specification.  After equation (5) of
arXiv:2512.16486v1 (Section 1.3) the paper writes:

> It is a general fact that a positive specification is characterised by its
> singleton part, see [15] Theorem 1.33.  Hence, for `φ` to be `Φ`-Gibbs it is
> enough to have, for `φ`-a.e. `ω`, `φ(ω(e)=1 | F_{⟨e⟩})(ω) = p` or
> `p/(p+q(1-p))` according as the two endpoints of `e` lie in the same block of
> `Φ_{⟨e⟩}(ω_{⟨e⟩})`.

That reduction — "the one-point part determines the law" — was not in the
repository.  It is proved here in the form the source states it: the conditional family is
*strictly positive* (every conditional probability lies in `(0,1)`), and then
the conclusion needs no further hypothesis on the laws.

The module works in the repository's own finite-law API (`OpenPath.FinProb`,
`Glauber.HasEdgeConditional`, `Glauber.edgeUpdate`) and instantiates the result
at the exact `p` / `p'` dichotomy of equation (2) of the source.

## Main declarations

File: `OnePointDetermination.lean` (namespace `Glauber.FinProb`).

| Declaration | Statement |
|---|---|
| `overwrite`, `overwrite_apply`, `overwrite_univ_eq` | Bookkeeping: overwriting a list of coordinates of a configuration sets exactly those coordinates (so any two configurations are joined by finitely many single-coordinate changes). |
| `ratio_update_eq` | Two laws with the same off-edge conditional family have the same mass ratio after any single-coordinate change. |
| `ratio_eq` | That mass ratio is globally constant. |
| `eq_of_shared_edgeConditionals` | **Two full-support finite laws on `E → B` sharing every off-edge conditional family coincide.** No positivity of the conditional masses is assumed. |
| `mass_eq_zero_iff_update`, `mass_eq_zero_iff` | With a strictly positive conditional family, the *vanishing* of the mass is invariant under single-coordinate changes (and hence under all changes). |
| `fullSupport_of_hasEdgeConditional` | A law satisfying a strictly positive conditional family automatically has full support. |
| `eq_of_shared_edgeConditionals_of_strictlyPositive` | **The one-point part determines the law for a positive specification**: two laws sharing a strictly positive off-edge conditional family coincide, with *no* full-support hypothesis on either law. |
| `refreshConj_mass`, `bind_refreshConj_mass` | The one-step mass computation of a conjugated heat-bath refresh (extracted from the existing `refreshConj_invariant` proof). |
| `hasConjConditional_of_invariant`, `hasEdgeConditional_of_invariant` | Invariance under a refresh implies the corresponding product conditional factorization. |
| `invariant_iff_hasEdgeConditional` | Invariance under `edgeUpdate c e` is *equivalent* to satisfying the conditional family `c` at `e`. |
| `eq_of_forall_invariant` | **Uniqueness of the invariant law**: two full-support laws invariant under the same singleton heat-bath family coincide. |
| `ofPMF_fkPMF_mass_pos` | At `0 < q`, `0 < p < 1` every finite random-cluster configuration has strictly positive mass. |
| `eq_fkPMF_of_shared_conditionals` | A full-support law with the random-cluster singleton conditionals is the random-cluster law. |
| `openRate_mem_Ioo`, `edgeConditionals_strictlyPositive` | The equation-(2) open rate lies in `(0,1)` at interior parameters, so the random-cluster conditional family is a *positive* specification. |
| `hasEdgeConditional_of_openRate_odds` | The odds form of the equation-(2) dichotomy forces the random-cluster conditional family. |
| `eq_fkPMF_of_openRate_odds` | **The paper's one-point part identifies the random-cluster law.** A law whose one-edge conditional probabilities are `p` when the endpoints are connected in the off-edge configuration and `p' = p/(p+q(1-p))` otherwise *is* `G.fkPMF`. No full-support hypothesis on the law: interior parameters make the conditional family strictly positive, which forces full support. |

The last statement uses the repository's existing `Glauber.FKBridge.openRate`
and `Glauber.FKBridge.fk_hasEdgeConditional`, so it is the *same* one-edge
conditional law as equation (2) of the source, not a re-statement of it.

## Proof shape

Inside one off-edge fibre of coordinate `e`, both laws factor through the same
conditional law `c e off`, so their mass ratio is constant on the fibre.  A
single-coordinate change stays inside one fibre, and any two configurations are
joined by finitely many single-coordinate changes (the `overwrite` chain), so
the ratio is a global constant `c`.  Summing over all configurations and using
`∑ μ.mass = ∑ ν.mass = 1` gives `c = 1`.  The random-cluster instantiation
reads the odds form `μ(true|off)(1-r) = μ(false|off) r` together with
`μ(true|off) + μ(false|off) = outsideMass` to recover `μ(·|off) = boolLaw r`.

## Full support is essential (calibration)

`FullSupportNecessary.lean` proves that the full-support hypothesis of
`eq_of_shared_edgeConditionals` cannot be dropped.  On the two-point coordinate
type there are *distinct* laws with the *same* off-coordinate conditional
family:

* `muEx = δ_{00}` and `nuEx = (δ_{00} + δ_{11})/2`;
* the shared family is `otherFamily e off = δ_{off (otherCoord e)}`, i.e. "the
  bit at the other coordinate".

Both `hasEdgeConditional_muEx` and `hasEdgeConditional_nuEx` are proved, and
`muEx_ne_nuEx` separates the laws by their mass at the all-open configuration
(`0` versus `1/2`).  `onePoint_determination_needs_fullSupport` packages this
as a single existential statement.  The mechanism is exactly the missing
denominator: `muEx` gives zero mass to the fibre obtained by flipping both
coordinates, so the two laws' singleton conditionals cannot see the difference.

So the source's word *positive* in "a positive specification is characterised
by its singleton part" is a real hypothesis, not exposition.

## Exact verification

Toolchain `leanprover/lean4:v4.35.0` (the repository's `lean-toolchain`), using
the repository's own built `.lake` artifacts and default heartbeats:

```
export LEAN_PATH=<repo>/results/fk-qcritical/.lake/build/lib/lean:<all package .lake/build/lib/lean>
lean OnePointDetermination.lean
```

Result: success.  `#print axioms` for all eighteen declarations reports exactly
`[propext, Classical.choice, Quot.sound]`; see `audit.log`.

`FullSupportNecessary.lean` is checked the same way; its four `#print axioms`
lines report exactly the same three axioms (`audit-full-support.log`).

A scan for `sorry`, `admit`, `unsafe` and `axiom` declarations finds none in
either file.

## What this does *not* prove

This is a finite statement.  It does **not** assert any infinite-volume DLR
equation, and it does not by itself close Proposition 1.8(2).  Precisely, the
two steps still missing are the following, and they are the residuals:

1. **Limit passage (analysis).**  Let `μ` be an `IsFKLimit exh hq hp α μ`.  One
   must show that for each fixed edge `e` and `μ`-a.e. `ω`, the limit's
   one-edge conditional probability equals the random-cluster value for the
   limiting boundary convention.  In the free/`⊥`-boundary case the connection
   event for `e` is monotone along the exhaustion and the indicator is lower
   semicontinuous, so a Portmanteau plus monotone-convergence argument should
   give this; the wired case needs the at-most-one-infinite-cluster input.  This
   step is *not* formalised here.
2. **Fibre assembly.**  From "the global one-edge conditional probabilities are
   the specification's" one must deduce `B.IsDLR hq hp α hα μ` at a finite box
   `B`, i.e. the compProd identity
   `Measure.map B.splitEquiv μ = B.exteriorMeasure μ ⊗ₘ B.fkKernel hq hp α hα`.
   This needs the two-step conditional expectation identity
   `μ(·|F_{E∖{e}}) = E[μ(·|F_{E(B)^c}) | F_{E∖{e}}]` together with a
   disintegration of `μ` along `B.splitEquiv`; the repository's
   `CanonicalDisintegration` module is about finite PMFs, not about this
   disintegration, so it is not directly reusable.  This module supplies the
   *fibrewise* content of step 2 (`eq_of_shared_edgeConditionals`: a fibre law
   with the specification's one-point part *is* the specification), but not the
   disintegration itself.

Once (1) and (2) are available, `B.IsDLR` at every box follows, and with the
already-proved `ConventionTransport.mem_dlrMeasures_of_atMostOne` (all
conventions agree a.e. under at-most-one infinite exterior cluster) this yields
Proposition 1.8(2) for limits whose singleton conditionals are the free
ones — a strictly larger class than the coherent-convention closure currently
recorded in `PROOF-STATUS.md`.

## Independent-use notes

* `eq_of_forall_invariant` gives uniqueness of the full-support invariant law of
  the singleton heat-bath chain of Section 3 *without* the bit-positivity
  hypothesis `hbit` required by `FiniteComparison.mixture_tendsto`, because it
  never passes through convergence.
* `ratio_eq` is the general "one-point part determines a full-support law on a
  finite product" statement and is independent of the random-cluster model.
* `ofPMF_fkPMF_mass_pos` is a reusable strict-positivity fact at interior
  parameters.
