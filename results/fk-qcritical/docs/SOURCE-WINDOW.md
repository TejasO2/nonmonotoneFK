# Source upper-window assembly for Theorem 1.10

Public module: `FK.SourceWindow`.

This closes the downstream Proposition 4.2 / AG / source-uniqueness interface.
Its principal declarations are
`FK.SourceWindow.theorem_1_10_full_window_q_lt_one` and
`FK.SourceWindow.theorem_1_10_full_window_one_lt_q`. It is **not** an
unconditional proof of Theorem 1.10.

For fixed `q`, `0 < q < 1` or `1 < q`, these declarations construct a positive
`δ'`, uniform over all `p ≤ 1`, such that

`max p (fkPrime p q) < criticalProb G o + δ'`

implies that `SourceFKMeasures` is a singleton and its unique law is almost
surely nonpercolating. The family is the arbitrary-exhaustion, all-region
source family from `FK.SourceUniqueness`, not a metric-convention subclass.

## Exact remaining inputs

After selecting `D : SourceEnhancementDevices G`, a pivotal edge `e₀`, and
`roots`, the full-window theorem requires precisely:

1. **The AG strict shift.** For `q < 1`,

   `DeactivationShift (Percolating G) (criticalProb G o) D.Scycle`.

   For `1 < q`, `D.Sstar` replaces `D.Scycle`. This input is not proved here.

2. **Literal nested equation (9).** For every interior `0 < p < 1`,

   `NestedEquationNine hq hp1.le (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le) roots`.

   This includes the actual ordinary nested-box arm estimate for the selected
   upper Bernoulli law. The adaptive construction and vanishing arm estimate
   remain separate obligations.

No separate stochastic-dominant, nonpercolation, weak-limit-existence,
fixed-exhaustion, Theorem 5.1, or Proposition 1.8(2) hypothesis remains in the
two full-window declarations. Their graph inputs are connectedness, `0 <
criticalProb G o < 1`, the chosen devices and these two named inputs. The
module concerns `q ≠ 1`; `FK.QOneLine` handles the classical line separately.

## What is discharged

- `upperLaw_dominates_q_lt_one` and `upperLaw_dominates_one_lt_q`: Proposition
  4.2 dominates every source weak limit on every induced vertex exhaustion by
  the exact AG upper product.
- `isSourceFKLimit_tail`: truncation preserves a source weak limit and its
  outer-boundary schedules.
- `exists_tail_nonempty_edges`: after one fixed edge enters the exhaustion,
  every tail box has nonempty edge type. This discharges Prop 4.2's technical
  premise without altering the original limit.
- `upperLaw_eq_ltUpperParameters` and `upperLaw_eq_gtUpperParameters`: exact
  identification with the upper weights used by `EssentialWindow.UpperWindow`.
- `sourceFKMeasures_zero`: the all-closed point mass is the unique source law
  at `p = 0`, and it is nonpercolating. Compactness supplies membership and a
  direct open-walk argument supplies nonpercolation.
- In the full-window statements the radius is shrunk below
  `1 - criticalProb`, excluding `p = 1`; `p = 0` is handled separately and
  needs no nested-equation input.

`exists_pivot_and_sourceEnhancementDevices` supplies the device package from
the existing source-graph hypotheses, including a pivotal edge with a cycle
and double-ray certificate. This geometric existence theorem does not prove
the strict enhancement shift of those devices.

## Verification

The fourteen principal declaration audits are in `Audit.lean`. They use only
`propext`, `Classical.choice`, and `Quot.sound`. Run `./check.sh` from
`results/fk-qcritical`; source fidelity to an unconditional Theorem 1.10 is
deliberately **not** claimed while its two substantive inputs remain open.
