Public module: `FK.OneEdgeNoEscape`, with fully qualified audit names and 22 principal allowed-axiom checks. The main result is a criterion of which hypotheses yield the scalar identity: `scalar_iff_limsup_le`, `scalar_iff_farVanishing`, and assembled geometric no-escape one-point/IsDLR data. The provided moving-atom counterexample rules out an automatic conclusion from mere weak convergence. This does not relieve the source of its actual FK-specific escape estimate.

# No-mass-escape for the one-edge one-point limit passage

Scope, exact statements, audit, and the precise residual for the one-point
determination route to Proposition 1.8(2) (direction 1 of the present stage).

Sources: `OneEdgeNoEscape.lean` (1033 lines), audited in `NoEscapeAudit.lean`.
Builds against `FK.OneEdgeLimit` at public `main`
`babe333a1769743687f12ea8c30aaa85109b5f7d`, Lean `v4.35.0`, default
heartbeats. All 22 audited declarations report exactly
`[propext, Classical.choice, Quot.sound]`; the file contains no `sorry`,
`admit`, `axiom` or `unsafe` declaration.

## The residual this file addresses

`FK/OneEdgeLimit.lean` reduces the per-edge one-point conditional identity of an
infinite-volume limit law to the single scalar mass identity

```
hscalar :  ∫⁻ ρ dμ = μ {ω | B.splitBit e ω = true}
```

for the limiting two-valued rate `ρ`, and proves the one-sided limit theorem
`onePoint_edge_of_scalar` which turns `hscalar` into the actual one-point
identity (and hence `B.IsDLR` at the box). Two things were left open there:

1. the **rate identification**, that `ρ` is the random-cluster value of the
   limiting geometric specification, and
2. **no mass escape**, the half of `hscalar` that weak convergence alone does
   not give.

This file closes (1) completely and turns (2) into an exact, sharp criterion:
`hscalar` is *equivalent* to a no-mass-escape inequality, and no-mass-escape is
`equivalent* to a small-box (far-vanishing) inequality. It also proves that the
remaining inequality cannot be obtained from the measure-theoretic hypotheses
alone, so that it is genuinely a statement about the FK model.

## 1. The rate is two-valued — `openRate_eq_twoValuedRate`

`Glauber.FKBridge.openRate` is, definitionally,

```
openRate ξ e off = if endpointsConnectedWithout G ξ e (offConfiguration G ξ e off)
                   then ↑p else FK.prime q p,      FK.prime q p = p / (p + q(1-p)).
```

Therefore the limiting rate `ω ↦ openRate (αspec (splitOff ω).1) e (splitOff ω).2`
is `twoValuedRate p (FK.prime q p) Cinf` for the *actual box-graph connection
event*

```
Cinf = {ω | endpointsConnectedWithout B.graph (αspec (splitOff ω).1) e
              (offConfiguration B.graph (αspec (splitOff ω).1) (splitOff ω).2)}.
```

So the a.e. rate-identification hypothesis `hrate` of `onePoint_edge_of_scalar`
is **not an extra input**: once `Cinf` is the box's connection event, it holds
by definition (`onePoint_edge_of_noEscape_geometric` discharges it).

The two orientation lemmas fix which monotonicity direction the model has:

* `lt_prime_iff  : p < FK.prime q p ↔ q < 1`  (for `0 < p < 1`, `0 < q`),
* `prime_lt_iff  : FK.prime q p < p ↔ 1 < q`.

Hence for `q < 1` the rate takes the *smaller* value `p` on the connection
event: increasing the connection events decreases the rate, so the antitone
machinery of `OneEdgeLimit` applies and the automatic half is the `liminf`
one. For `q > 1` the orientation is reversed and the increasing-rate mirror
would be needed instead.

## 2. The scalar identity is equivalent to no mass escape — `scalar_iff_limsup_le`

Setting: `μs : ℕ → ProbabilityMeasure (Configuration E)` with `μs k ⇀ μ`, an
increasing family of **clopen** events `C k` with union `Cinf`, and constants
`0 ≤ α < β ≤ 1`. Suppose the finite-stage laws satisfy the one-point identity
with the two-valued connection rates:

```
hstage : ∀ k, μ_k {e open} = ∫ twoValuedRate α β (C k) dμ_k .
```

(`stage_eq_of_fin` proves that this follows from the constant test `g ≡ 1` in
the finite-stage one-point identity `hfin` of `OneEdgeLimit`, so it is available
whenever `hfin` is.) Then

```
hscalar  ↔  limsup_k μ_k(C k) ≤ μ(C∞).
```

The proof has two ingredients.

* **Automatic half** (`le_of_tendsto_measure_toReal_of_monotone_clopen`): if the
  masses `μ_k(C k)` converge to `L` then `μ(C∞) ≤ L`. This is the `liminf` half
  and needs only that clopen sets have null frontier.
* **Algebra**: `hstage` forces `μ_k(C k) → L = (μ{e open} - β)/(α - β)`, and
  `hscalar` is literally `μ{e open} = β - (β-α)μ(C∞)`. Since `μ(C∞) ≤ L`
  always, the scalar identity is equivalent to `L = μ(C∞)`, i.e. to
  `limsup_k μ_k(C k) ≤ μ(C∞)`.

`tendsto_measure_iff_scalar` records the equivalent `Tendsto` form: no mass
escape is precisely the convergence `μ_k(C k) → μ(C∞)`.

## 3. The small-box form — `scalar_iff_farVanishing`

The escape mass is exactly the mass of the finite-stage connection events whose
witness is forced to leave a fixed box:

```
hscalar  ↔  ∀ ε > 0, ∃ m, ∀ᶠ k, μ_k(C k \ C m) ≤ ε .
```

This is the form in which the residual input is a statement about a *fixed*
finite box `C m`, uniformly in the exhaustion `k`. Both directions are proved
(`scalar_of_farVanishing`, `scalar_iff_farVanishing`); the reverse direction
uses monotone continuity `μ(C m) ↑ μ(C∞)` and the exact split
`μ_k(C k) = μ_k(C m) + μ_k(C k \ C m)` for `k ≥ m`.

## 4. Sufficient conditions

* `scalar_of_eventually_eq`: if the connection events stabilise
  (`C k = C K` for all `k ≥ K`) then there is no escape. This covers graphs in
  which a connection has a unique finite witness: for a forest graph with a
  free (or otherwise tree-compatible) boundary partition the off-edge
  connection event is empty, so the connection masses are constant in `k`.
* `scalar_of_agreesOnEvents`: if `μ_k(C k) = μ(C k)` for all `k` — i.e. the
  finite-stage law agrees with the limit on the event itself, as in product /
  `q = 1` / restriction-consistent models — then there is no escape.
* `scalar_of_dominated`: if `μ_k(C∞) ≤ μ(C∞)` for all `k` then there is no
  escape.

## 5. Sharpness: the escape half is not automatic — `exists_massEscaping`

There are increasing clopen events `C k` with union `Cinf`, probability measures
`μs k ⇀ μ`, such that

```
μ_k(C k) = 1  for every k,   but   μ(C∞) = 0,
```

hence `limsup_k μ_k(C k) = 1 > 0 = μ(C∞)`. The construction is explicit and in
`Configuration ℕ`: `μs k = δ_{pt (k+1)}` (the configuration with a single open
edge at `k+1`), `μ = δ_{all closed}`, `C k = {ω | ∃ j ∈ {1,…,k+1}, ω j = open}`.
The witness of `C k` *moves off to infinity*, which is exactly the escape
phenomenon: every hypothesis of §2 except the escape inequality holds.

Consequently the residual inequality in `OneEdgeLimit` cannot be discharged by
measure theory alone; it requires FK-specific input — stabilisation, agreement
on the events, domination by the limit, or vanishing far-connection mass. This
is the precise sense in which the one-point determination route needs the model.

## 6. Assembly

`onePoint_edge_of_noEscape` is `FiniteBox.onePoint_edge_of_scalar` with

* the rates specialised to `twoValuedRate α β (C k)`,
* continuity of the stage rates derived from clopenness of `C k`,
* the range bounds derived from `0 ≤ α < β ≤ 1`,
* the monotonicity of the rates derived from `C k ⊆ C (k+1)` and `α ≤ β`,
* the pointwise rate limit derived from `C k ↑ Cinf`,
* `hscalar` replaced by `limsup_k μ_k(C k) ≤ μ(C∞)` via §2.

`onePoint_edge_of_noEscape_geometric` specialises further: `Cinf` is the actual
box-graph connection event of the specification and the a.e. rate
identification is discharged by `openRate_eq_twoValuedRate`.

## 7. What remains for the FK free-boundary exhaustion

For the free boundary convention and an exhaustion `Λ k ↑ E`, the finite-stage
rate is the two-valued rate of `C k = {ω | the endpoints of e are connected
inside Λ k without e}` and the limiting rate is the two-valued rate of the same
connection event in the whole off-configuration; this is the `q`-orientation
case of §1. What must still be proved is exactly

```
limsup_k μ_k(C k) ≤ μ(C∞)      (equivalently  μ_k(C k) → μ(C∞)),
```

i.e. the connection probabilities of the exhaustion converge to the limit law's
connection probability; the `liminf` inequality is automatic. §5 shows this
cannot be deduced from the remaining hypotheses, and §4 lists the classes in
which it is immediate. The genuine remaining analytic content is therefore a
*uniform far-connection estimate* for the actual FK laws — a statement about FK
geometry, not about the limiting martingale.

## Build and audit

```
export LEAN_PATH=<repo>/results/fk-qcritical/.lake/build/lib/lean:...   # plus the package builds
lean -o OneEdgeNoEscape.olean OneEdgeNoEscape.lean
LEAN_PATH="$LEAN_PATH:." lean NoEscapeAudit.lean
```

`audit.log` (produced by the second command) reports, for all 22 principal
declarations, exactly `[propext, Classical.choice, Quot.sound]`.


## Follow-up: geometric reductions

`FK.ClopenEscape` and `FK.ClusterEscape` now prove far vanishing both from a
decreasing clopen escape family with vanishing limit intersection and from
measurable increasing escape events controlled by a dominating law. They also
prove the direct exterior-wiring escape lemma and vanishing escaping-cluster
tails under nonpercolation. See [the escape note](CLOPEN-ESCAPE.md). These are
conditional DLR reductions: the actual nested finite stage, source connectivity
partition and, outside a dominating nonpercolating regime, the clopen escape
family are still open. No general Proposition 1.8(2) conclusion is claimed.
