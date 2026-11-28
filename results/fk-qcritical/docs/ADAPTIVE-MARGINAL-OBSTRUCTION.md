# Fixed-stage adaptive-marginal obstruction

`FK.AdaptiveMarginalObstruction` gives an exact finite counterexample to the
fixed-stage averaging inference proposed for an arbitrary-dominant random
frontier argument. The candidate marginals are both the fair law, so this is
**not** a counterexample to DLR uniqueness or Theorem 5.1. It is also not a
cofinal reverse-martingale result.

## The coupling and conditional stages

The accepted ordered Bool coupling is transported to configurations on `Unit`:

| lower | upper | mass |
|---|---|---:|
| false | false | $1/4$ |
| false | true | $1/4$ |
| true | true | $1/2$ |
| true | false | $0$ |

Both candidate coordinates have the fair $(1/2,1/2)$ marginal and the upper
has $(1/4,3/4)$. At upper-open, the selected finite region is the whole
coordinate set; at upper-closed it is empty, with its unique incident edge
closed. The frontier is a decreasing function of region cardinality, and every
selected region has the required closed frontier.

The marked event is that the coordinate is open. At the full region,
`outsideSigma` is the bottom sigma algebra and the fair conditional expectation
is the unconditional fair mass $1/2$. At the empty region, `outsideSigma` is
all measurable sets and the conditional expectation is the event indicator;
a closed frontier forces this indicator to zero. These are exact kernel
computations, not axioms or approximate identities.

The resulting fixed-region identifications satisfy the hypotheses of the
accepted `ae_condExp_eq_of_dominated_coupling_frontier` and
`integral_condExp_eq_of_dominated_coupling` theorems literally. The ordered
triple has the required product-marginal and pointwise-order laws. Nevertheless,
the common conditional-stage integral is

$$0\cdot{1\over4}+{1\over2}\cdot{3\over4}={3\over8},
$$

while the original fair-coordinate open mass is $1/2$. The proved defect is
$1/2-3/8=1/8$, for both original candidate conditionals.

## Why the averaging step fails and what remains

The selected region depends on the upper coordinate, which is correlated with
the original lower configuration under the ordered coupling. In particular,
the full conditional region can occur with a lower-closed configuration. Its
conditional expectation need not average to the original lower mass when
integrated over the product coupling. The fixed-region fibre identities and
common joint-stage values do not restore a tower identity for that different
measure.

This closes the original-marginal alternative left open by
`CouplingSealCounterexample`. A successful uniqueness proof must instead use a
genuine cofinal limiting/martingale mechanism, a new conditional-stage
identity, or different marginals with constructed joint control. It cannot
assume the displayed fixed-stage averaging identity from the current
interfaces alone.

The entire source was rebuilt with Lean 4.35 at default heartbeats, with seven
independent axiom reports, each using only `propext`, `Classical.choice`, and
`Quot.sound`.
