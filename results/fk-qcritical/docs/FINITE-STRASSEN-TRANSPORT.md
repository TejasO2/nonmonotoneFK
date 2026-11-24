# Ordered couplings from stochastic domination (Strassen, hard direction)

Public modules: `FK.FiniteTransport` and `FK.CountableOrderedCoupling`. The coordinator rebuilt with pinned **Lean 4.35**, rather than the earlier draft's Lean 4.33. The only repair was in `exists_cylinder_ordered_coupling`: the two retired `Measure.isProbabilityMeasure_map` references were replaced by `(Measure.isProbabilityMeasure_map_iff ...).2 inferInstance`. All 13 principal audits pass the standard-axiom checker. No infinite gluing theorem is claimed.


`Transport.lean` in this directory. Self-contained: `import Mathlib` only, no project
imports, no `sorry`/`admit`/`axiom`/`unsafe`.

## What is proved (all sorry-free, axioms audited)

1. **`FiniteTransport.exists_transport`** — the finite transportation lemma.
   For finite `X Y`, a relation `R : X → Y → Prop`, masses `a : X → ℝ`, `b : Y → ℝ`
   with `0 ≤ a`, `0 ≤ b`, `∑ a = ∑ b`, and the Hall condition
   `∑_{x∈S} a x ≤ ∑_{y ∈ N_R(S)} b y` for every `S : Finset X`,
   there is `π : X → Y → ℝ` with `0 ≤ π`, `∑_y π x y = a x`, `∑_x π x y = b y`
   and `¬ R x y → π x y = 0`.

2. **`FiniteTransport.finite_strassen`** — Strassen's theorem, hard direction, on an
   arbitrary **finite preorder** `α`: if probability measures `μ ν` on `α` satisfy
   `μ A ≤ ν A` for every upper set `A`, then there is a **coupling** `κ` on `α × α`
   with `κ.map Prod.fst = μ`, `κ.map Prod.snd = ν`, `IsProbabilityMeasure κ` and
   `∀ᵐ z ∂κ, z.1 ≤ z.2`. No independence, support or full-support hypothesis.

3. **`FiniteTransport.finite_strassen_boolean`** — the same for `{0,1}^E`, `E` finite,
   pointwise order (the FK configuration space).

4. **`FiniteTransport.finite_strassen_probabilityMeasure`** — the same with
   `ProbabilityMeasure (E → Bool)` arguments in the project's convention
   (`FKLimit.StochasticallyDominates ν μ` is `μ A ≤ ν A` for measurable upper `A`;
   compare `docs/ERRATA-AND-DEVIATIONS.md`, "Stochastic order and new versus legacy
   APIs"). For a finite configuration space every set is measurable.

5. **`FiniteTransport.finite_strassen_iff`** — both directions: domination on upper
   sets ⟺ existence of an ordered coupling with exact marginals
   (`stochasticallyDominates_of_orderedCoupling` is the converse).

6. **`FiniteTransport.exists_cylinder_ordered_coupling`** — countable `E`: domination
   on `E → Bool` passes to every finite coordinate set `S`, and the two `S`-marginals
   admit an ordered coupling with exact marginals.

7. **Transfer corollaries** (directly the "hdom" use): `lintegral_le_of_orderedCoupling`
   and `lintegral_le_of_stochasticallyDominates` (every measurable increasing
   `f : α → ℝ≥0∞` has `∫⁻ f dμ ≤ ∫⁻ f dν`, no integrability hypothesis),
   `measure_zero_of_stochasticallyDominates` (an upper event null under `ν` is null
   under `μ`), and `finite_strassen_setConfig` (`Set V` with inclusion, i.e. `FK` bond
   configurations rather than `V → Bool`).

8. `CountablePrep.lean` (separate file, also sorry-free): the measure-theoretic
   identities of the Cantor space that the countable lift starts from —
   `proj n x = fun i : Fin n => x i`, `measurable_proj`, `graphMap n = fun x => (proj n x, x)`,
   `graphMap_fst`, `graphMap_snd`, the disintegration identity
   `μ.map (graphMap n) = (μ.map (proj n)) ⊗ₘ (μ.map (graphMap n)).condKernel`,
   and `order_eq_all_levelOrder` (the full order is the intersection of the finite
   level orders). This pins the residual exactly; it asserts no countable theorem.

## Proof strategy (no linear programming duality)

`exists_transport` is by strong induction on `|S| + |T|` for the support-normalised
problem (`a` vanishes exactly off `S`, `b` off `T`, both positive there):

* a nonempty proper **tight** set `U` (`a(U) = b(N U)`) splits the problem into the two
  independent problems `(U, N U)` and `(S∖U, T∖(N U))`; Hall is inherited on the first
  and derived (via `a(V∪U) ≤ b(N V ∪ N U)`, using that the second column set misses
  `N U`) on the second;
* otherwise pick a certified pair `x₀ ∈ S`, `y₀ ∈ N {x₀}` with `b y₀ > 0` and subtract
  `t := min{a x₀, b y₀} ∪ {b(N V) − a(V) : V ⊆ S∖{x₀}, y₀ ∈ N V}`, all of whose
  entries are positive by no-tightness. Hall is preserved in all three cases of the
  `x₀ ∈ V` / `y₀ ∈ N V` case split, and either a support element disappears (induction
  on the support) or a new tight set appears (previous bullet). The subtracted mass is
  returned as the point mass at `(x₀,y₀) ∈ R`.

`finite_strassen` derives the Hall condition from domination: the up-closure of `S` is
an upper set containing `S`, so `μ S ≤ μ (N S) ≤ ν (N S)`; the transportation lemma
then yields `π`, and `κ := ∑_{p} ofReal (π p.1 p.2) • δ_p` is a probability measure
whose singleton masses are `ofReal (π p.1 p.2)`, with marginals `μ`, `ν` (checked on
singletons via `Measure.ext_of_singleton`) and order support `π p.1 p.2 = 0` off the
order.

## Build, audit, times

Toolchain in this VM: Lean 4.33.1 with a fully built Mathlib on `LEAN_PATH`
(the project pins 4.35; only long-stable Mathlib API is used).

```
lean CountablePrep.lean     # ~2-4 s
lean Transport.lean         # ~4-7 s with warm imports; no errors, no sorry
```

Scripted audit (`cat Transport.lean` + `#print axioms`, then `lean`): every listed
declaration depends on axioms `[propext, Classical.choice, Quot.sound]` only:
`exists_transport`, `split_tight`, `transport_aux`, `finite_strassen`,
`finite_strassen_boolean`, `finite_strassen_probabilityMeasure`, `finite_strassen_iff`,
`stochasticallyDominates_of_orderedCoupling`, `exists_cylinder_ordered_coupling`,
`lintegral_le_of_orderedCoupling`, `lintegral_le_of_stochasticallyDominates`,
`measure_zero_of_stochasticallyDominates`, `finite_strassen_setConfig`.
`CountablePrep.lean` needs no audit (no `sorry`, no axioms beyond the Mathlib ones used
by `Measure.condKernel`).

## Scope, and what is **not** proved

This closes the *finite* (equivalently finite-volume) form of the Strassen direction,
which is the form used for finite FK laws (`finiteVolumeLaw`, `FK.Phases.StochLe`,
nested finite couplings), and it is the combinatorial core of the infinite statement.
It is **not** a measure-level theorem for countably infinite coordinate sets, and
nothing here is a paper-level theorem of the FK source.

Residual for the countable lift (precisely): the missing ingredient is a
**gluing lemma** — for countable `E`, finite `S`, probability measures `μ ν` on
`E → Bool` and an ordered coupling `π` of the two `S`-marginals, produce a coupling
`κ` of `μ` and `ν` whose `S × S`-marginal is `π`. That is a disintegration statement
(`Measure.condKernel` for the finite-coordinate projection, requires
`StandardBorelSpace (E → Bool)`, available for `E = ℕ`), and it feeds the standard
compactness assembly: the sets
`K_S := {κ : ProbabilityMeasure (C × C) | κ.map fst = μ, κ.map snd = ν, κ({z | z.1|S ≤ z.2|S}) = 1}`
are closed (Portmanteau for the closed order set), nested, and nonempty by the
gluing lemma, so `IsCompact.inter_iInter_nonempty` yields `κ` ordered on every finite
`S`, hence a.s. This assembly is **not** formalised here; the file proves everything
up to it plus the level-wise statement (6).

Also not claimed: strictness/equality cases of the domination order, and any statement
about the FK critical parameters.
