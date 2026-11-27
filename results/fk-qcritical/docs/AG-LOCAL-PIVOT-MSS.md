# Local-pivot MSS transport and cylinder analytic windows

Public modules: `FK.AGLocalPivotMSS` and `FK.AGCylinderLocalPivot`.

This proves the probabilistic transport part of the Aizenman--Grimmett
enhancement argument from actual bounded-local pivot-modification maps.
Essentialness by itself is not shown to construct those maps, and arbitrary
quasi-transitive rerouting remains outside the result.

## Uniform local trade

For a finite Boolean product law, let a map `T e` change only coordinates in
`R e` and send every `e`-pivotal configuration to one with some pivotal
candidate enhanced coordinate. The modification regions have size at most `N`,
each candidate is nominated by at most `K` source coordinates, and every Boolean value
under each coordinate law has mass at least `δ`. Then
`sum_pivot_le_of_local_modifications` proves

$$
\delta^N\,\operatorname{pivotTotal}(r,A)
 \le 2^N K\,\operatorname{pivotOn}(S,r,A).
$$

No injection of the maps and no disjointness of candidates is required.
Candidate overlap is charged by `K`, while bounded-local likelihood transport
charges the product weights. `exists_uniform_pivotTrade_of_local_modifications`
normalizes these to a positive constant `c = δ^N / (2^N K)`, uniform across
indices sharing the same bounds. The target candidates really belong to the
enhanced subtype `S`.

## Arbitrary-coordinate cylinder windows

The primary endpoints are
`decrement_AGInput_of_cylinder_local_modifications` and
`increment_AGInput_of_cylinder_local_modifications`.

Here `A` and `An n` are events on one arbitrary countable coordinate type. Each
`An n` is a genuine increasing cylinder on the finite `support n`. Derivatives
and pivot sums are computed on that support, while target mass, limit, and the
final zero/one conclusion remain on the unrestricted ambient `A`. Thus these
are not finite-coordinate wrappers disguised as infinite-volume results.

Both mean-value arguments are confined to the repaired clamp-free compact
window and use actual cylinder restrictions of the derivative. The decrement
endpoint gives a point strictly above `pc` at which decrement-profile mass is
zero; the increment endpoint gives a point strictly below `pc` at which
increment-profile mass is one. These are the analytic inputs used by the FK
phase-window bridges, not a completed graph assembly.

## Explicit remaining inputs

The theorems keep all of the following premises visible:

1. `DependsOnCoordinates (An n) (support n)`, increasing `An n`, and measurable
   increasing `A`;
2. an actual local pivot map with bounded modification regions and bounded
   candidate nomination;
3. a uniform positive lower mass bound for all coordinate values throughout
   the critical window;
4. convergence of the approximants to the target mass and the appropriate
   zero-enhancement subcritical or supercritical baseline;
5. `0 < pc < 1` and the parameter-window conditions.

The first three are not derived from essentialness. No two-linkage/rerouting
theorem, arbitrary quasi-transitive map construction, general enhancement
conjecture, or BFO Theorem 1.4 is asserted. The BBR literature identifies the
failed general rerouting step and repairs specified lattices, not the general
quasi-transitive setting; nothing in this analytic transport removes that gap.
