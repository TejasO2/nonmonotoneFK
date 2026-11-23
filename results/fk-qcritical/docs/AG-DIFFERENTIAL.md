# Finite AG differential comparison for the one-edge OR gadget

## Result

`AGDifferential.lean` composes the public finite Margulis--Russo formulas with
the public one-edge OR pivot comparison. It contains no edits to shared files.

The main declaration is

```
FK.AGGadget.enhancedEvent_differential_comparison
```

For an arbitrary finite increasing event `B`, uniform bond/activation rates
`p,s` in `[0,1]`, and a common lower bound `δ` for both values of every
coordinate law, put

- `Dp = Σ_e Pjoint(e is bond-pivotal for enhancedEvent B)`;
- `Ds = Σ_e Pjoint(e is activation-pivotal for enhancedEvent B)`.

The theorem internally proves both `HasDerivAt` formulas for the product
polynomial, with respective derivatives `Dp` at `p` and `Ds` at `s`, and proves
`(δ / 2) * Dp ≤ Ds`. This is the finite analogue of the differential step

```
∂s τ_L(p,s) ≥ g(p,s) ∂p τ_L(p,s)
```

described as equation (3) in the outline of the AG argument. It does not assume
either derivative formula or the pivot inequality as a conclusion-shaped
premise: the former are proved here, and the latter is applied from
`sum_edgePivotal_event_mul_le`.

The supporting declarations `hasDerivAt_configurationWeight_left/right`,
`hasDerivAt_eventWeight_left_raw/right_raw`, and
`hasDerivAt_eventWeight_left_pivotal/right_pivotal` prove simultaneous
bond-only and activation-only differentiation on a disjoint union of bond and
activation coordinates. In particular, activations are not discarded from the
product space. `eventWeight_eq_uniformJointLaw_event` identifies the
polynomial at unit-cube parameters with the actual normalized `jointLaw`.
The polynomial formulation is valid without division at `p,s = 0,1`.

`enhancedEvent_differential_comparison_pos` specializes to the explicit

```
orMinorant p s = min (min p (1-p)) (min s (1-s))
```

and proves positivity of `orMinorant p s` for `0 < p,s < 1`, its continuity on
`ℝ × ℝ`, the two mass bounds, and `(orMinorant p s / 2) * Dp ≤ Ds`.
`enhancedArm_differential_comparison` applies the general result to the actual
`enhancedArmEvent G o n`, for a graph whose edge type is finite.

There are 25 audited declarations in total, including simp lemmas. The source
compiled with no warnings on the final check. No `sorry`, `admit`, `unsafe`, or
new `axiom` is used. Every axiom report is exactly the standard list
`[propext, Classical.choice, Quot.sound]`; see `AGDifferentialAudit.txt`.

## Explicit residuals and blockers

- This proves only the already constructed one-coordinate OR enhancement. It
  does not prove deterministic local implantation of a general bounded-range
  enhancement. The latter needs the missing arbitrary-radius annular
  star/cycle rewiring and its bounded-fibre conversion of a bond pivot into an
  activation pivot.
- No integral comparison along differential curves is asserted. Deriving it
  requires choosing and analyzing integral curves for a comparison field and
  transporting the finite-arm monotonicity along those curves.
- No limit as the arm radius tends to infinity is asserted. Comparing the weak
  derivatives after that limit, or upgrading finite-arm monotonicity to the
  limiting percolation function, remains separate work.
- Consequently this is not Theorem 1.4, Theorem 1.8, or an unrestricted AG
  strict critical-point shift. The finite graph hypothesis in the one-arm
  corollary is deliberately visible as `Fintype G.edgeSet`.

## Verification

From `results/fk-qcritical/`, with no generated output in the shared tree:

```sh
export ELAN_HOME="$PWD/../../.scratch/elan"
export PATH="$PWD/../../.scratch/elan/bin:$PATH"
lake env lean ../../.ultramath/smwsq4fkq/m2/AGDifferential.lean
lake env bash -c 'cd ../../.ultramath/smwsq4fkq/m2 &&
  lean -o AGDifferential.olean AGDifferential.lean'
lake env bash -c 'set -o pipefail; cd ../../.ultramath/smwsq4fkq/m2 &&
  export LEAN_PATH="$PWD:$LEAN_PATH" &&
  lean AGDifferentialAudit.lean | tee AGDifferentialAudit.txt'
```

The final source check and independent olean build passed with Lean 4.35.0.
The import-based audit passed all 25 declarations.
