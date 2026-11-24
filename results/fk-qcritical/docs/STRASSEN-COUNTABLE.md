# Countable Strassen ordered coupling (`E → Bool`)

Public module: `FK.StrassenCountable`. Independently rebuilt using Lean 4.35 / current public `FK` imports, with all 20 principal declarations allowed-axiom checked. The earlier "countable lift missing" report in `FINITE-STRASSEN-TRANSPORT.md` is now historical: this module closes that abstract measure-level gap. It does not itself close any FK-specific conditioning, one-point limit, random-exhaustion reversal or critical-window obligation.


Direction 1 of swarm `smwu2ryc1`.  This closes the measure-level countable lift that
`results/fk-qcritical/docs/FINITE-STRASSEN-TRANSPORT.md` records as missing:

> Residual for the countable lift (precisely): the missing ingredient is a **gluing
> lemma** — for countable `E`, finite `S`, probability measures `μ ν` on `E → Bool` and an
> ordered coupling `π` of the two `S`-marginals, produce a coupling `κ` of `μ` and `ν`
> whose `S × S` marginal is `π`. … it feeds the standard compactness assembly: the sets
> `K_S := {κ | κ.map fst = μ, κ.map snd = ν, κ({z | z.1|S ≤ z.2|S}) = 1}` are closed …,
> nested, and nonempty by the gluing lemma … This assembly is **not** formalised here.

Both the gluing lemma (with the exact `S × S` marginal) and the compactness assembly are
now formalised.  Nothing in the shared tree was modified.

## Files

| path | contents |
|---|---|
| `StrassenCountable.lean` | the whole development (835 lines, `import Mathlib`, `import FK.FiniteTransport`, `import FK.CountableOrderedCoupling`, `import FK.Proposition42`) |
| `AuditStrassen.lean` | `#print axioms` audit of the 20 principal declarations |
| `build.sh` | compiles a file against the pinned project build (`LEAN_PATH` from `~/.fk_lean_path`) |
| `STRASSEN-COUNTABLE.md` | this note |

Build (pinned Lean 4.35 toolchain and the project's own `.lake` build):

```
export LEAN_PATH="$(cat ~/.fk_lean_path):$(pwd)"
~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean StrassenCountable.lean   # 3 s warm
~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean AuditStrassen.lean
```

Result: **0 errors, 0 warnings**; every audited declaration depends on
`[propext, Classical.choice, Quot.sound]` only; no `sorry`, `admit`, custom `axiom`,
`unsafe` or `native_decide` occurs in the source (`grep` clean).

## What is proved (namespace `CountableStrassen`, `E` countable, `C := E → Bool`)

* `projF S : C → (S → Bool)`, `graphF S : C → (S → Bool) × C`, `levelOrderF S`,
  `order_eq_iInter_levelOrder : {z | z.1 ≤ z.2} = ⋂ S : Finset E, levelOrderF S`.
* `condKernel_fibre_eq_one` : for the graph law `ρ = μ.map (graphF S)` and
  `k = ρ.condKernel`, `∀ᵐ a ∂(μ.map (projF S)), k a {x | projF S x = a} = 1`.
  Proof: `ρ` is carried by the graph set `G = {(a,x) | a = x|_S}`, hence
  `((μ.map projF) ⊗ₘ k) Gᶜ = 0`; `Measure.compProd_apply` turns this into the vanishing
  of `∫⁻ a, k a (fibre a)ᶜ` and `lintegral_eq_zero_iff` gives the a.e. statement.
* **`exists_glued_coupling`** (finite-coordinate conditional fibre extension):

  ```
  (π : Measure ((S→Bool) × (S→Bool))) [IsProbabilityMeasure π]
  (h1 : π.map fst = μ.map (projF S)) (h2 : π.map snd = ν.map (projF S))
  (hord : ∀ᵐ a ∂π, a.1 ≤ a.2)
  ⊢ ∃ κ, IsProbabilityMeasure κ ∧ κ.map fst = μ ∧ κ.map snd = ν ∧
        κ.map (Prod.map (projF S) (projF S)) = π ∧ κ (levelOrderF S) = 1
  ```

  Construction: `kμ = (μ.map (graphF S)).condKernel`, `kν` likewise,
  `κ0 = kμ.comap fst ×ₖ kν.comap snd`, `κ = κ0 ∘ₘ π`.  The exact cylinder marginal uses
  the fibre support twice: `(kμ a.1).map (projF S) = dirac a.1` (checked on singletons of
  the finite space) and `Measure.map_prod_map`, so
  `κ0.map (Prod.map projF projF) =ᵐ[π] Kernel.deterministic id`, whence
  `κ.map (Prod.map projF projF) = π`.  The order statement uses
  `(kμ a.1).prod (kν a.2) (levelOrderF S) ≥ kμ a.1 (fibre a.1) * kν a.2 (fibre a.2) = 1`
  for `π`-a.e. ordered `a` and `Measure.bind_apply`.
* `goodSet μ ν S` = probability measures with the two marginals and full order on `S`;
  `isClosed_goodSet` (continuous marginal maps via `ProbabilityMeasure.continuous_map`,
  Portmanteau `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` for the closed level
  set, using `isClosed_iff_forall_filter`), `goodSet_nonempty` (from
  `FiniteTransport.exists_cylinder_ordered_coupling` plus the gluing lemma),
  `goodSet_antitone` (`S ⊆ T ⇒ goodSet T ⊆ goodSet S`).
* **`exists_orderedCoupling_of_dominates`** — countable Strassen, hard direction:

  ```
  (hdom : ∀ A, MeasurableSet A → IsUpperSet A → μ A ≤ ν A)
  ⊢ ∃ κ : ProbabilityMeasure (C × C), κ.map fst = μ ∧ κ.map snd = ν ∧
      ∀ᵐ z ∂κ, z.1 ≤ z.2
  ```

  Proof: `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` applied to the
  directed family `goodSet μ ν` in the compact space `ProbabilityMeasure (C × C)`
  (`instCompactSpaceProbabilityMeasure`); the countable intersection of the level orders has
  full mass by `measure_iUnion_null` on the complements, and `order_eq_iInter_levelOrder`
  upgrades it to the full pointwise order.
* `exists_orderedCoupling_support` : same, with `κ {z | z.1 ≤ z.2} = 1`.
* `strassen_iff` : `(∀ upper A, μ A ≤ ν A) ↔ ∃ ordered coupling with exact marginals`
  (the converse is `FiniteTransport.stochasticallyDominates_of_orderedCoupling`).
* `lintegral_le_of_stochasticallyDominates` (monotone `ℝ≥0∞` observables),
  `measure_eq_zero_of_stochasticallyDominates` (null upper events transfer down).
* **Projective-limit form.**  `OrderedCylinderSystem μ ν` = a family
  `law S : Measure ((S→Bool) × (S→Bool))` that is a probability law with the two
  `S`-marginals, is a.e. ordered, and is compatible under restriction
  (`(law T).map (Prod.map (projSub h) (projSub h)) = law S` for `S ⊆ T`).

  `exists_global_coupling_of_system` : every such system is the cylinder system of a global
  ordered coupling `κ`, i.e. `κ.map (Prod.map (projF S) (projF S)) = law S` for every `S`.
  Conversely `cylinderSystem` builds an `OrderedCylinderSystem` from any global coupling
  with the two marginals and a.e. order, and `nonempty_orderedCylinderSystem_self` proves
  the class is inhabited by the diagonal system of a single measure `μ` (built from the
  diagonal graph law, no domination input).
* `exists_orderedCylinderSystem` : domination ⇒ the class of ordered cylinder systems is
  inhabited (derived from the main theorem, hence not independent evidence).
* `FKLimit.exists_orderedCoupling_of_stochasticallyDominates` and
  `FKLimit.exists_orderedCoupling_support_of_stochasticallyDominates` : the same statements
  in the project's own convention `FKLimit.StochasticallyDominates ν μ` on
  `Configuration E = E → Bool`, ready to plug into the `hdom` slot of
  `FK/Theorem110Assembly.lean` / `FK/SubcriticalPercolation.lean`.

## Scope, and precise residuals

* This is the **abstract Strassen direction only**.  No FK-specific statement (finite-volume
  laws, DLR equations, `FiniteBox.HasOnePointConditionals`, one-point determination,
  Theorem 1.4/1.10/1.11) is proved or claimed here; the file makes no use of `FK` beyond the
  finite transport theorem, the countable preparation file and the `StochasticallyDominates`
  definition.
* The **selection problem** — producing a *compatible* family of ordered cylinder couplings
  for a given pair `μ ν` — is *not* solved.  `OrderedCylinderSystem` is explicit input;
  `exists_orderedCylinderSystem` derives it from the main theorem (so it is not independent),
  and `nonempty_orderedCylinderSystem_self` is non-circular only for `μ = ν`.
  `exists_orderedCoupling_of_dominates` / `strassen_iff` do not need any such system.
* No statement about strictness of domination, equality cases, or uniqueness/optimality of
  the coupling.
* Configurations are `E → Bool` (bond open/closed) with the pointwise order.  The
  `Set E`-configuration and labelled-multigraph-setoid forms are not restated here (they are
  measurably and order-isomorphic; no effort was spent on the transfer).
* `[Countable E]` is used for the standard-Borel/compact product structure on `E → Bool`
  (`StandardBorelSpace`, `CompactSpace`, `HasOuterApproxClosed` are all found by instance
  search for countable `E`).
