# The finite FK law on affine component counts is Bernoulli percolation

Member m4, swarm smwu2ryc1.  Source: `ForestBernoulli.lean` (namespace
`FK.ForestBernoulli`), audit: `AuditForest.lean` + `audit.log`.
Toolchain: the repository's pinned `leanprover/lean4:v4.35.0` (via
`.scratch/elan`), `LEAN_PATH` = the repository's `.lake/build/lib/lean` plus
every package build dir.  Default heartbeats.  No `sorry`/`admit`/`axiom`/
`unsafe`; every audited declaration depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## What is proved

The repository proves only the `q = 1` identity
(`LabelledMultigraph.fkPMF_q_one`: at `q = 1` the finite random-cluster law is
`bernoulliProductPMF p`).  This file proves the missing `q ≠ 1` statement on the
class of graphs whose component count is affine in the number of open labels,
together with its forest instance.

### 1. Main theorem (arbitrary boundary setoid)

```
theorem fkPMF_eq_bernoulliProductPMF_of_affine
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (C : ℕ)
    (hk : ∀ ω : G.Configuration, G.componentCount ξ ω + openCount ω = C)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.fkPMF hq hp1.le ξ =
      G.bernoulliProductPMF (p := fkMod q p) (fkMod_le_one hq hp0 hp1)
```
with `fkDen q p = p + q * (1 - p)` and `fkMod q p = p / fkDen q p`.  That is:
the normalized FK PMF is the independent Bernoulli product with parameter
`p / (p + q(1-p))`, the paper's `fkPrime p q`.

The proof is an exact weight factorization, not a ratio/coupling argument:
`one_label_factor` shows per label that
`p = q * (D/q) * r` and `1 - p = 1 * (D/q) * (1 - r)` with `D = p + q(1-p)`,
`r = p/D`; consequently `edgeWeight p ω = q^{openCount ω} * (D/q)^{|E|} *
edgeWeight r ω` (`edgeWeight_eq`), and the hypothesis `hk` turns the `q`-power
into the constant `q^C * (D/q)^{|E|}`, which cancels against the partition
function (`sum_edgeWeight`).

### 2. Labelled forests

```
theorem fkPMF_eq_bernoulliProductPMF_of_labelledForest
    (G : LabelledMultigraph) (hG : G.IsLabelledForest) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.fkPMF hq hp1.le G.freeBoundary =
      G.bernoulliProductPMF (p := fkMod q p) (fkMod_le_one hq hp0 hp1)
```
`IsLabelledForest` is the repository's existing acyclicity predicate (every
labelled edge is a bridge in the all-open configuration, so loops and cycles are
excluded).  The affine count is the repository's
`componentCount_add_openCard_of_free_isOpenForest` with `C = |V|`.

**So: the random-cluster model on any finite labelled forest with free boundary
is Bernoulli percolation with parameter `p/(p + q(1-p))`, for every interior
`q > 0`.**  At `q = 1` this is `fkPMF_q_one`.

### 3. Exact partition function

```
theorem partitionFunction_of_affine
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (C : ℕ)
    (hk : ∀ ω, G.componentCount ξ ω + openCount ω = C)
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.partitionFunction q p ξ = q ^ C * (fkDen q p / q) ^ (Fintype.card G.Edge)
```
and, for a free-boundary labelled forest,

```
theorem partitionFunction_of_labelledForest (G) (hG : G.IsLabelledForest) ... :
    G.partitionFunction q p G.freeBoundary =
      q ^ Fintype.card G.Vertex * (fkDen q p / q) ^ (Fintype.card G.Edge)
```
i.e. `Z = q^{|V|} ((p + q(1-p))/q)^{|E|}`.  `fkWeight_of_affine` is the
per-configuration factorization they rest on.

### 4. Corollaries and non-vacuity

* `fkPMF_apply_of_labelledForest`: the mass form
  `fkPMF ... ω = (edgeWeight (fkMod q p) ω : ℝ≥0∞)`.
* `fkPMF_q_one_of_affine`: at `q = 1` the theorem returns
  `bernoulliProductPMF p`, agreeing with `fkPMF_q_one`.
* `fkMod_one : fkMod 1 p = p`; `fkMod_coe_real`:
  `(fkMod q p : ℝ) = p / (p + q(1-p))`, i.e. exactly `FK.Theorem14.fkPrime`.
* `le_fkMod_of_q_le_one : p ≤ fkMod q p` for `q ≤ 1`, and the strict form
  `lt_fkMod_of_q_lt_one : p < fkMod q p` for `q < 1`, `0 < p < 1`: in the
  antiferromagnetic regime the `q`-factor pushes the effective edge parameter
  *up* (the mechanism behind the paper's `le_fkPrime_of_q_le_one`).
* `twoV_fkPMF_open_gt`: on the single-edge graph with `q < 1` the edge is
  strictly more likely to be open than under independent `p`-percolation.
* Explicit instance `twoV` (two vertices, one labelled edge, free boundary),
  `C = 2`: `twoV_fkPMF_eq_bernoulliProductPMF`, and
  `twoV_fkPMF_open : twoV.fkPMF ... (fun _ => true) = (fkMod q p : ℝ≥0∞)`.
* Sharpness `twoEdgeCycle_not_affine`: on the two-vertex two-parallel-edge
  cycle no `C` satisfies the hypothesis (all-closed: `2 + 0 = 2`; all-open:
  `1 + 2 = 3`), so the affine hypothesis is not vacuous and cannot simply be
  dropped; there the `q`-power genuinely depends on the configuration.

## Mathematical scope and precise residuals

* Everything is finite: no infinite-volume law, DLR equation, weak limit,
  critical point, or percolation probability is asserted.
* The theorem is stated for the repository's normalized `fkPMF` on arbitrary
  finite labelled multigraphs with arbitrary boundary setoids; the hypothesis is
  the arithmetic condition `componentCount + openCount = C`, verified for
  free-boundary labelled forests.
* Not proved here: a *stochastic-domination* corollary (only the scalar
  parameter comparison `p ≤ fkMod q p` is proved) (FK on a forest
  dominating Bernoulli `p` when `q ≤ 1`).  That needs a bridge from
  `bernoulliProductPMF` to the `FKLimit.bernoulliProduct` (unit-interval-
  indexed) representation used by
  `FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le`; the
  comparison itself is then immediate from `le_fkMod_of_q_le_one`.
* Not proved here: the analogous statement for graphs with cycles (false in
  general — the cycle certificate above), and no claim that every
  `IsFKLimit` or DLR law is of this form.
