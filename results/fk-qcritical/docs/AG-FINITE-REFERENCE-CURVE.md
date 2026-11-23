# Finite-family independent reference curves

`AGFiniteReferenceCurve.lean` works on the whole admissible comparison line for
a finite independently activated sleeve family. Moved base bonds use
$p-ct$, selected activation coordinates use $s+t$, and unmoved coordinates stay
at their original rates. Here $c$ is the established
`independentComparisonSpeed a b R`. Annuli may overlap; the established union
sum, rather than disjointness, controls their contribution.

`unitLineOfBox` constructs genuine unit-interval rates at every intermediate
time, using both initial and terminal parameter-box hypotheses. `armCurve`
and `percolationCurve` are the actual independent-product probabilities of the
enhanced finite arm and enhanced infinite root cluster, converted to real
numbers through `ENNReal.toReal`.

`monotone_armCurve` proves monotonicity at every radius on `Icc 0 T` from the
finite trace polynomial. `monotone_percolationCurve` orders every approximating
arm and applies continuity from above for the two actual product measures;
it does not exchange a derivative with an infinite-volume limit.
`percolationCurve_eq_zero_of_le` and
`percolationCurve_pos_of_pos_of_le` provide backward-zero and forward-positive
phase propagation along this reparametrized curve.

The explicit endpoint is

$$T_{\max}=\min\!\left(\frac{p-a}{c},\,b-s\right).$$

The module proves its nonnegativity and, when $a<p$ and $s<b$, its positivity.
Every admissible elapsed time is at most $T_{\max}$; conversely
$cT_{\max}\le p-a$ and $T_{\max}\le b-s$ place both endpoint parameters in
`Icc a b`. `monotone_percolationCurve_maximalTime` discharges those endpoint
inputs internally and gives the canonical comparison on `Icc 0 Tmax`.
The speed is independent of the finite device-index cardinality.

These are non-strict probability and phase comparisons for a finite family.
They do not prove an infinite-index derivative limit, strict critical shift,
essential-enhancement window, `hAG`, or any whole-paper theorem. Countability,
local finiteness/connectivity and common positive annulus cardinality are
explicit where used; the arm theorem itself does not require countability.

## Verification

The exact source was independently rebuilt with pinned Lean 4.35.0/default
heartbeats. Seventeen principal declarations independently passed the
repository's allowed-axiom validation. All source audits contain only the three
standard Lean axioms, and no placeholders or custom declarations are used.
The public release check verifies the integrated module and its documentation.
