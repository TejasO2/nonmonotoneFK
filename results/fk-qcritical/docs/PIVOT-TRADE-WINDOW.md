# Pivot-trade obstruction and compact-window repair

Public modules: `FK.PivotTradeObstruction`,
`FK.PivotTradeObstructionCycle3`, `FK.PivotTradeWindow`,
`FK.PivotTradeAGRepair`, and `FK.PivotTradeAGRepairIncrement`.
They correct an unsatisfiable geometric premise in the repository's
pivot-trade reduction. They do not correct or contradict the paper.

## The old whole-region constant does not exist

`FK.AGMassDerivative.decrement_AGInput_of_pivotTrade` asks for one constant
$c>0$ with

$$c\,P_{\mathrm{total}}(b,\varepsilon)\le
  P_{\mathrm{on}}(b,\varepsilon)$$

throughout every approximation index and $0<\varepsilon<b<1$. That range is
too large. The minimal cycle devices already show why.

On two parallel bonds with enhanced first bond and connection event “at least
one bond open”, the exact masses are

$$P_{\mathrm{on}}=1-b,\qquad
  P_{\mathrm{total}}=2(1-b)+\varepsilon.$$

On the simple triangle with enhanced direct bond and an auxiliary two-bond path,
they are

$$P_{\mathrm{on}}=1-b^2,\qquad
  P_{\mathrm{total}}=1-b^2+2b(1-b+\varepsilon).$$

In both cases the auxiliary bonds satisfy the cycle-device complement
condition, and the enhanced bond is genuinely essential. Nevertheless, for
fixed $\varepsilon>0$, $P_{\mathrm{on}}/P_{\mathrm{total}}\to0$ as $b\to1$.
`not_uniform_pivotTrade` and `not_uniform_pivotTrade_tri` give explicit
counterexamples for every $c>0$. The obstruction applies to the proposed
whole-region reduction, not to the paper's Glauber-dynamics comparison. The
increment profile on the parallel gadget has a separate explicit trade bound
with constant $1/2$, recorded as a one-sided non-obstruction.

## Per-event compact-window constants

`PivotTradeWindow` proves continuity of product-polynomial event weights and
pivotal masses. On the open weight cube, an off-pivotal weight is strictly
positive exactly when there is an off-edge configuration in which the edge is
essential. Consequently, a nonempty enhanced set all of whose edges are
essential has strictly positive enhanced pivotal mass.

On a compact subset of the open cube, continuity supplies a positive minimum
of that mass and a finite maximum of total pivotal mass. The explicit choice
`min pivotOn / (max pivotTotal + 1)` therefore produces a positive constant
for the whole compact set. Decrement and increment box corollaries specialize
this to the parameter regions traversed by the trade lines. These results are
per event, not a uniform bound over an approximation sequence.

## Corrected mean-value reduction

The two AG-repair modules re-run the mean-value argument only on

$$b\in[p_c/2,(1+p_c)/2],\qquad
  0<\varepsilon\le\min(p_c/4,(1-p_c)/4),$$

using the actual interior derivatives from `AGMassDerivative` and proving the
moving base coordinate remains in that window. Conclusions have the same
zero/one profile-mass form as the older `decrement_AGInput_of_pivotTrade` and
increment companion, including the final enhancement-size upgrade.

The replacement hypothesis is a **single constant uniform in $n$** on that
window. Constant approximating sequences establish satisfiability, not that
property for a genuine family of arm events. Compactness by itself gives
nothing uniform in $n$. The finite-approximation convergence `hconv` and the
subcritical/supercritical baseline `hbase` also remain open.

Therefore no universal essential-enhancement trade bound, strict critical
shift, Theorem 1.4, Theorem 1.10, or Theorem 1.11 is claimed. The original
whole-region pivot premise should not be presented as an available reduction
input; use the window form while recording its remaining approximation-
uniformity requirement.

All five sources were independently rebuilt at default heartbeats with pinned
Lean 4.35.0. The 35 selected principal axiom audits (the submitted audits after
deduplication) contain only `propext`, `Classical.choice`, and `Quot.sound`.
