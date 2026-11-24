Public module: `FK.OneEdgeLimit`. Independently rebuilt with eight principal allowed-axiom checks. Its stale early-header "automatic" scalar wording was corrected during integration: it is not a theorem that mass escape vanishes automatically. The proved exact scalar criterion and its DLR corollary retain all rate-continuity, monotone, weak-convergence, scalar mass and geometric rate-identification hypotheses; only liminf of the increasing clopen events is automatic.

# One-edge one-point conditionals through an infinite-volume weak limit

Scope, exact declarations, build, and residuals for
`.ultramath/smwu2ryc1/m1/OneEdgeLimit.lean` (direction `d6`, "one-edge
conditionals through infinite-volume limits").

## Setting (all inside the repository's own API)

* `E : Type*` with `[Countable E]`; `Configuration E = E → Bool` (the
  repository's `FKLimit.Configuration`), a compact second-countable space whose
  Borel and product σ-algebras agree.
* `B : FK.InfiniteVolume.FiniteBox E`, `e : B.edges`.
* `Y := B.Exterior × Glauber.OffConfig Bool B.edges e` — the off-edge box data.
* `B.splitBit e : Configuration E → Bool` is the bit at `e` and
  `B.splitOff e : Configuration E → Y` is the off-edge projection (both
  continuous, `continuous_splitBit`, `continuous_splitOff`).
* For `φ : BoundedContinuousFunction Y ℝ`, `offTest φ ω = φ (B.splitOff e ω)`
  and `openBitTest φ ω = if B.splitBit e ω = true then offTest φ ω else 0`.
* The target is `FK.InfiniteVolume.FiniteBox.HasOnePointConditionals`: for every
  box edge `e` and every measurable `g` of `Y`,
  `∫⁻ 1{e open}·g(off) dμ = ∫⁻ openRate(α η, e, off)·g(off) dμ`.

## Proved declarations (no `sorry`, no custom axiom, no `unsafe`)

| Declaration | Statement |
|---|---|
| `finiteVolumeLaw_hasOnePointConditionals` | **Finite stage.** For every box `B`, boundary setoid `β` and `0<q`, `0<p<1`: the actual finite-volume FK law `B.finiteVolumeLaw hq hp β` satisfies `B.HasOnePointConditionals (fun _ => β)` — the box's own equation-(2) one-point identity with its own constant wiring. |
| `finiteVolumeLaw_hasOnePointConditionalsBif`, `hasOnePointConditionals_iff_bif` | `bif`-normal form of the same statement and the equivalence with the library form (instance-robust, used to bypass dependent `Decidable` mismatch). |
| `fkMeasure_singleton_true_eq` | Per-off-edge form of equation (2) for the finite random-cluster measure (`FKF.fkMeasure_singleton_odds` in the `fibreConfig` shape). |
| `finiteStage_real` | Real-integral form of the finite-stage identity for bounded continuous nonnegative off-edge tests. |
| `onePoint_le_of_antitone_rates` | **One-sided limit passage.** Let `μs k ⇀ μ`. Let `ρs k : Configuration E → ℝ` be continuous, `[0,1]`-valued, decreasing pointwise to `ρ`, and suppose each `μs k` satisfies the one-point identity with rate `ρs k`. Then for every bounded continuous `φ : Y → ℝ` with `0 ≤ φ`, `∫ openBitTest φ dμ ≤ ∫ ρ·offTest φ dμ`. |
| `onePoint_eq_of_scalar_continuous` | **Two-sided limit passage.** Under the same hypotheses plus `Measurable ρ`, `0 ≤ ρ` and the single scalar mass identity `∫⁻ ofReal ρ dμ = μ {e open}`, the limit satisfies the exact identity `∫ openBitTest φ dμ = ∫ ρ·offTest φ dμ` for every bounded continuous `φ ≥ 0`. |
| `integral_openBitFactor_mul`, `integrable_rate_mul`, `offTest_le_norm`, … | Reusable integrability/continuity plumbing used above. |
| `le_liminf_measure_of_monotone_clopen` | **Automatic half of the scalar identity.** If `C k` are clopen, increasing, with union `C∞`, and `μs k ⇀ μ`, then `μ C∞ ≤ liminf_k μs k (C k)`. |
| `lintegral_pushforward_restrict_eq`, `lintegral_pushforward_withDensity` | The two `splitOff`-pushforward lintegrals in terms of the real integrals: `∫⁻ ψ d((μ.restrict {e open}).map splitOff) = ofReal ∫ openBitTest ψ` and `∫⁻ ψ d((μ.withDensity (ofReal ρ)).map splitOff) = ofReal ∫ ρ·offTest ψ`. |
| `map_splitOff_restrict_eq_withDensity` | **Pushforward equality.** The continuous-test one-point identity forces `(μ.restrict {e open}).map (splitOff e) = (μ.withDensity (ofReal ρ)).map (splitOff e)` (via `ext_of_forall_lintegral_eq_of_IsFiniteMeasure` on the compact box off-space). |
| `onePoint_edge_of_scalar` | **Per-edge one-point conditionals of the limit law.** With the finite-stage identities, continuous decreasing rates `ρs k ∈ [0,1]` with pointwise limit `ρ`, weak convergence `μs k ⇀ μ`, the scalar mass identity `∫⁻ ofReal ρ dμ = μ{e open}`, and `ρ = openRate B.graph (α η) e off` `μ`-a.e., the limit satisfies `∫⁻ 1{e open}·g(off) dμ = ∫⁻ openRate B.graph (α η) e off ·g(off) dμ` for **every measurable** `g` of the off-edge data — i.e. exactly the per-edge content of `FiniteBox.HasOnePointConditionals`. |
| `hasOnePointConditionalsBif_of_edge_scalar` | **Box level.** Per-edge data for all `e : B.edges` with one common specification `α` give `B.HasOnePointConditionalsBif α μ` for the limit law. |
| `isDLR_of_edge_scalar` | **DLR of the limit at the box.** With `0<q`, `0<p<1` and measurable `α`, the same inputs give the actual Dixon–Vere-Jones identity `B.IsDLR hq hp₁.le α hα μ`, through `FiniteBox.isDLR_of_hasOnePointConditionals`. |

Build: Lean 4.35.0 (`leanprover/lean4:v4.35.0`) against the repository's built
`FK` oleans and its vendored Mathlib; commands and environment are in
`build.sh`. `Audit.lean` reports exactly `[propext, Classical.choice,
Quot.sound]` for all declarations above.

## Mathematical content and why it is not a wrapper

The finite-stage identity is a genuine finite computation inside the actual
normalized `fkMeasure` (via equation (2)); it is *not* the hypothesis of the
limit theorems restated. The limit theorems are proved by
* rewriting the finite-stage identity in real-integral form,
* the Portmanteau half `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`
  applied to the continuous cylinder tests `openBitTest φ` and
  `ρ_m·offTest φ`,
* the two-sided sandwich `ρ_k ≤ ρ_m` (`k ≥ m`) plus monotone/dominated
  convergence in the rate index for the decreasing-rate direction,
* and the `‖φ‖ - φ` complement trick for the reverse inequality, which uses the
  scalar mass identity exactly once.

So the whole "Portmanteau plus monotone convergence" limit step of
`docs/ONE-POINT-DETERMINATION.md` (its residual 1) is discharged relative to two
explicit inputs.

## Precise residuals

* **(R1) No mass escape.** The scalar identity
  `∫⁻ ofReal ρ dμ = μ {e open}` is *not* automatic. Only its `liminf` half
  (`le_liminf_measure_of_monotone_clopen`) follows from weak convergence. The
  missing half is `lim_k μs k (C k) = μ C∞` for the increasing clopen
  connection events `C k` of the exhaustion, i.e. a uniform-in-volume
  negligibility of connections formed outside a fixed box. In the free
  two-valued shape `ρs k = p' + (p - p')·1_{C k}` the scalar identity is
  *equivalent* to that statement, so it is exactly the residual.
* **(R2) Geometric identification of the rate.** One must identify the
  pointwise limit `ρ = lim_k ρs k` with the box specification's value
  `openRate B.graph (α η) e off`. Along a free-boundary exhaustion
  `ρs k` is two-valued (`p` on the box-`k` connectivity event, `p'` off it); the
  identification is a purely deterministic statement relating connectivity in
  the box-`k` graph to exterior wiring at the box `B` (it needs the exhaustion's
  vertex/incidence coherence; `FiniteBox` carries an unrelated vertex type per
  box, so this is genuine data).
* **(R3) Measurable test functions.** *Discharged*: `onePoint_edge_of_scalar`
  is the measurable-test statement, obtained from the continuous-test identity by
  the `splitOff`-pushforward equality
  (`map_splitOff_restrict_eq_withDensity`) plus
  `withDensity`/`restrict` lintegral computation. It remains per-edge; the
  conjunction over `e : B.edges` (with per-edge rate data) is exactly
  `HasOnePointConditionalsBif`, and `isDLR_of_hasOnePointConditionals` then gives
  the box DLR identity. Gluing the per-edge statements into the single
  `HasOnePointConditionals` of the box requires only packaging the per-edge data;
  no new mathematics.
* **(R4) Finite-stage rates are genuine.** For the actual exhaustion,
  `hfin` of `onePoint_edge_of_scalar` is available from
  `finiteVolumeLaw_hasOnePointConditionals` at each stage with
  `ρs k ω := openRate (box k).graph (α k) e (off_k ω)`, which is a continuous
  cylinder function (box `k` data only) — so that hypothesis is not vacuous.

## End-to-end statement obtained

`isDLR_of_edge_scalar` is the complete chain in one declaration: for a
`BoxExhaustion`-stage family of finite-volume laws now converged to `μ`, with
per-edge continuous two-valued rates decreasing to a limiting rate that is
`μ`-a.e. the box specification's equation-(2) open rate and satisfying the scalar
mass identity at each edge, the limit law satisfies `B.IsDLR` at that box.  Every
measure-theoretic step of that chain is proved here; what remains outside is
`(R1)` (the scalar identity) and `(R2)` (the identification of the limiting
rate), both of which are properties of the exhaustion geometry and the model,
not of the limit passage.

No claim is made that these residuals are vacuous, and no unconditional
`one-point`/`IsDLR` statement for an infinite-volume limit is asserted.  The
finite-stage statement `finiteVolumeLaw_hasOnePointConditionals` is
unconditional, and `onePoint_le_of_antitone_rates` is the sharp unconditional
limit inequality (in particular, monotone convergence of the rates plus weak
convergence alone cannot give the two-sided conclusion: that is precisely what
(R1) measures).
