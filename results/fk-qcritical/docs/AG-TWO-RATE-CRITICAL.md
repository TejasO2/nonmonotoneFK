# Exact two-rate critical curve of the activated two-class tree

Direction 6 (uniform AG reference-critical window from the two-class tree), realised as an
*exact* enhanced-versus-base critical-parameter comparison in the tree's own model class.

## Deliverable and verification

* Public source: `FK/AGTree/TwoRateCritical.lean`, namespace `Ultra`. It imports only
  `FK.AGTree.SharpThreshold`. No new dependencies or trust assumptions are introduced,
  no `sorry`/`admit`/custom axiom/`unsafe`/`native_decide` occurs, and heartbeat limits
  are left at their defaults.
* The exact source was independently rebuilt using the repository's pinned
  `leanprover/lean4:v4.35.0` and current dependencies. The only diagnostics are
  deprecation and minor linter warnings.
* Twenty fully qualified principal declarations are included in the public
  `Audit.lean`. Each reports exactly `[propext, Classical.choice, Quot.sound]`.
  Run `./check.sh` for the complete build, unique-audit, forbidden-declaration and
  documentation checks.

## Statements proved

Setup: the repo's `Ultra.law r` on the two-class tree `Ultra.G` (`Ultra.V` = reduced words
over `Fin 3 ⊕ Fin 2`), class-`0` edges open with probability `b = r 0`, class-`1` edges with
probability `s = r 1`, independently; `Perc` = "some vertex lies in an infinite open cluster".

1. `two_rate_criterion_full` — the complete phase criterion:
   * `2b + s + 4bs < 1 → pr r Perc = 0`;
   * `1 < 2b + s + 4bs → 0 < pr r Perc`;
   * `2b + s + 4bs = 1 → 0 < b → pr r Perc = 0`.
2. `critical_curve`, `critical_curve_div` — at activation `s` the base rate is subcritical
   below `critBase s = (1-s)/(2+4s)` and supercritical above it.
3. `critBase_zero`, `critBase_half`, `critBase_endpoints`, `critBase_continuousOn` —
   `critBase 0 = 1/2`, `critBase (1/2) = 1/8`, `critBase 1 = 0`, continuous on `[0,∞)`.
4. `critBase_strict_decrease`, `critBase_essential`, `critBase_antitone` — every positive
   activation rate strictly lowers the critical base rate, with `critBase s ≤ 1/2 - s/4`.
5. `enhanced_window`, `enhancement_strict_at_some_base`, `tree_reference_shift` — the
   AG-style strict shift at fixed base rate: for every `s > 0` there is `p < 1/2` with
   `0 < pr (enhRate p s) Perc` while `pr (enhRate p 0) Perc = 0`.
6. `percolation_at_paper_point`, `no_percolation_at_tenth_half`,
   `naive_bound_insufficient`, `critical_comparison_at_half`, `base_criterion_agrees` —
   consistency and sharpness: `(3/10, 1/2)` percolates (as previously proved) with exact
   critical base `1/8`; `(1/10, 1/2)` does **not** percolate although the crude one-type
   bound `3b + 2s = 13/10 > 1`; at `s = 0` the criterion reduces to the existing sharp
   base threshold `1/2`.
7. Infrastructure: `VClass` and exact class counts (`valid_class_*_card_*`), class
   dependence of the level-`n` and infinite forward-cluster probabilities (`pr_fwd_class`,
   `pr_cluster_class`), and the exact two-class fixed-point equations
   (`cluster_fixed`, `cluster_fixed_rep`, `cluster_fixed_zero`, `cluster_fixed_one`).

## Method (three genuinely different arguments)

* **Subcritical** (`2b + s + 4bs < 1`). Two-class first moment with the exact class counts
  (`2,2` valid letters at a class-`0` vertex, `3,1` at a class-`1` vertex) gives
  `pr{Fwd v (n+1)} ≤ (A p_n)_class(v)` for the mean matrix `A = !![2b,2s;3b,s]`; the
  explicit barrier `w = (1+s, 1+b)` satisfies `(A - I) w = (2b+s+4bs-1)(1,1)`, so on the
  subcritical side the barrier recursion is antitone, its limit `L ≥ 0` is a fixed point of
  `A`, and the elementary ratio argument shows `A` has no nonzero nonnegative fixed point
  when `2b+s+4bs < 1`. No spectral theory, no eigenvalues.
* **Supercritical** (`1 < 2b + s + 4bs`). An explicit sub-fixed point of the *exact*
  branching recursion: with `D = 2b+s+4bs-1` and `t = min(1/2, D/(6(K+1)))`, the vector
  `e = t·(1+s, 1+b)` satisfies both one-step inequalities, which reduce to two elementary
  two-variable polynomial inequalities (`poly_sq`, `poly_cu`). Induction gives the uniform
  bounds `e_class(v) ≤ pr{Fwd v n}` for all `n`, hence positive cluster probability.
* **Critical** (`2b + s + 4bs = 1`, `b > 0`). First-moment bounds degenerate here, so the
  exact fixed-point equations of the two class cluster probabilities are used instead.
  Multiplying by the left Perron vector `(1-s, 2s)` of `A` at criticality makes a
  nonnegative combination of the second-order remainders vanish, where
  `Q₀ = (u+v-uv)² + 2uv` and `Q₁ = u(v(3-3u+u²) + u(3-u))` with `u = b·pr{Cluster rep 0}`,
  `v = s·pr{Cluster rep 1}`; `Q₀ = 0` forces `u = v = 0`, and the equations then force both
  cluster probabilities to vanish.

## What this settles in the tree model class

* The paper's AG input (`hAG`: a strict shift of the enhanced critical parameter) is here a
  **theorem with the exact curve** `2b + s + 4bs = 1` — not a hypothesis, and not merely the
  previously known positivity at `(3/10, 1/2)`. The base threshold `1/2` is recovered as
  `critBase 0`, and essential activation (strict decrease for every `s > 0`) is proved with
  the explicit decrement `s/4`.
* No general quasi-transitive/bounded-range AG theorem is claimed: this is the tree model
  class only. The quasi-transitivity of the same tree is a separate direction.

## Precise remaining hypotheses / open cases

1. The single critical point `(b, s) = (0, 1)` is not decided by `two_rate_criterion_full`
   (it percolates deterministically: every activation edge is open and every activation
   vertex has an activation child, so the alternating activation path is open a.s.; that
   path argument is elementary but not formalised here). All other points of the curve
   `2b + s + 4bs = 1`, i.e. all with `b > 0`, are decided.
2. Nothing here covers the FK-parameter `hAG` of `FK/AGWindow.lean`, which concerns
  decrement-profile laws of `FKLimit.bernoulliProduct` on an abstract countable edge type —
  a different model; no statement of this file is an instance of it.
3. No DLR, strong-uniqueness or infinite-volume FK conclusion is drawn.

## Verification commands

From `results/fk-qcritical`, with the pinned toolchain:

```sh
lake env lean FK/AGTree/TwoRateCritical.lean
./check.sh
```

The module's last 20 lines are `#print axioms` commands. Those fully qualified commands
are also in `Audit.lean`, whose automated check requires uniqueness and the allowed
axiom set. This verifies the stated tree-model results; it does not promote them to the
paper's general AG or main-theorem statements.
