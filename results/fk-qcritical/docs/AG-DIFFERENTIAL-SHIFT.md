# Differential trade bound and strict parameter shifts

Public module: `FK.AGDifferentialShift`. This is an **analytic reduction**, not
the Aizenman–Grimmett essential-enhancement theorem and not Theorem 1.4.

**Follow-up:** `FK.AGMassDerivative` now proves the actual finite/cylinder
Fréchet derivative and pivotal formulas on the clamp-free interior, and repairs
the mean-value reduction there. Its one-edge witness proves that the older
closed-region `hderiv` premise written below is unsatisfiable on the collision
line. See [the derivative note](AG-MASS-DERIVATIVE.md); the geometric pivot
inequality remains unproved; the two ordinary reference baselines are supplied
by `FK.SubcriticalBaseline` and `FK.ReferenceBaseline`. A further check in
[the pivot-trade note](PIVOT-TRADE-WINDOW.md) proves that the old whole-region
pivot premise is actually false on minimal cycle devices. The available repair
uses per-event compact windows, retains approximation-uniformity explicitly,
and is not an AG theorem.

## Reference profiles and masses

`decrementWeight S b ε` puts weight `b - ε` on an enhanced set `S`, and
`incrementWeight S a ε` puts `a + ε` there. The values are clamped into the
unit interval. In their valid ranges, `decrementWeight_eq` and
`incrementWeight_eq` identify them with the public
`FK.EssentialWindow.decrementProfile` and `incrementProfile`, so the existing
reference window interfaces are used without a new model of Bernoulli weights.

`mass A S b ε` is the probability of `A` in `ℝ` under such a profile, with
`incMass` for increments. For an increasing event, larger decrements decrease
its mass and larger increments increase it. Monotone convergence from below
supplies the approximation convergence step: if `An` is monotone and has union
`A`, then masses of `An` converge to the mass of `A`, separately for every
profile.

The proofs also relate increments on `S` to decrements on `Sᶜ`, and establish
probability bounds from $0$ to $1$.

## Trade lines and signed derivative bounds

The mean-value helpers `le_of_deriv_nonpos` and `le_of_deriv_nonneg` are proved
from segment differentiability and Mathlib's slope formula.
`line_hasDerivAt` and `incLine_hasDerivAt` use the Fréchet derivative in the
`(base, enhancement)` plane and differentiate an affine trade line.

For an interior critical threshold `pc` and a constant `0<c≤1`, the
finite-approximation indices must have derivatives and trade signs

$$L_k(b,\varepsilon)(c,1)\le 0,\qquad
L_k(a,\varepsilon)(-c,1)\ge 0,$$

throughout the valid parameter regions, with `hbase` equal to a
nonpercolating phase and the percolating phase, respectively. For every finite
approximation, these signs force each trade line to decrease the first kind of
mass and increase the second kind.

`exists_subcritical_decrement` starts from an unmodified subcritical base
$b_0=p_c-c\varepsilon/2$ and proves that the base
$b_1=p_c+c\varepsilon/2$, with the decrement, is still nonpercolating.
`exists_supercritical_increment` dually starts from a supercritical base
$a_0=p_c+c\varepsilon/2$ and proves that the base
$a_1=p_c-c\varepsilon/2$, with the increment, is percolating.

`decrement_AGInput` and `increment_AGInput` shrink the enhancement slightly
where this is needed for strict positivity bounds, use monotonicity to return
to the requested enhancement, and package exactly the existing `hAG` inputs.
The four `upperWindow_of_decrementTrade_*` and
`lowerWindow_of_incrementTrade_*` theorems then assemble the existing
`UpperWindow`/`LowerWindow` statements. They do not replace or strengthen them
and do not include the missing FK comparison step; Proposition 4.2 is now
available separately in `FK.Proposition42Source`.

## Non-vacuity scope

Empty and full events demonstrate consistency of the hypotheses for the two
shift implications, with zero derivative data. They are **not** percolation
instances and carry no claim about a device or a positive critical threshold.

## What is still required for the actual AG theorem

1. **Real geometric trade inequality.** Instantiate it on the relevant
   bounded essential cycle/star devices and bounded critical parameter range.
   The estimate must be uniform for every finite approximation and every valid
   base/enhancement pair. Density alone does not supply it, because pendant
   edges can be dense but non-pivotal. Existing sleeve, all-bond covering,
   bounded-range example and tree results do not trivialize this step.
2. **Geometric use of the derivative/pivotal formula.** The follow-up proves
   finite and cylinder-restricted interior Fréchet derivatives and identifies
   them with pivotal masses. It does not establish the uniform pivot trade
   inequality from item 1, or identify support-local coefficients with an
   infinite `E`-indexed sum. The older closed-domain binder is repaired only
   on the interior, not globally differentiable through clamp collisions.
3. **Event approximation.** Choose `An` as the arm approximations to the
   percolation event, rather than unrelated events, and invoke the continuity
   helper proved above.
4. **Reference baselines.** `FK.SubcriticalBaseline` and
   `FK.ReferenceBaseline` now supply the ordinary subcritical and supercritical
   phases and zero-increment masses, with `ReferenceBaselinePercolating`
   adapting the latter to the window’s event. They do not supply the geometric
   trade, convergence or strict shift.
5. **Reference-to-FK assembly.** Combine the reference shift with the actual
   FK/DLR comparison and with Proposition 1.8's convention scope before
   claiming Theorems 1.4, 1.10 or 1.11.

The paper cites Michael Aizenman and Geoffrey Grimmett,
[Strict monotonicity for critical points in percolation and ferromagnetic models](https://link.springer.com/article/10.1007/BF01029985),
*Journal of Statistical Physics* **63** (1991), 817–835. The new module does
not prove that citation's estimate or silently adopt it as a theorem.

## Verification

The exact submitted module was independently rebuilt with the public imports
under the pinned Lean 4.35 at default heartbeats. Its 18 principal axiom
reports depend only on `propext`, `Classical.choice` and `Quot.sound`. The
public integration cleanup affects only deprecated tactics and unused binder
names; the complete repository check is still the release gate.


## Reference-baseline progress

The subcritical branch of `hbase` is now supplied by
`FK.SubcriticalBaseline.mass_percolating_eq_zero` on the actual percolation
event, using root-independent Bernoulli criticality; see
[the proof note](SUBCRITICAL-BASELINE.md). `FK.ReferenceBaseline` now supplies the supercritical baseline as well,
including enhanced weights in `ReferenceBaselinePercolating`.
The varying-arm geometric window trade and the reference shift are still
missing. Neither closes the unsatisfiable full-domain derivative binder.
