# Canonical metric-region split for nested FK comparisons

Deliverable: `NestedMetricRegionSplit.lean` (public import `FK.NestedMetricGeometry`).

## Constructed and proved

- `RegionSplit.vertexEquiv`, `edgeEquiv`, and the generic internal/external maps: a decidable vertex region of any finite indexed graph gives an exact vertex sum and an exact internal/external edge sum. Two `Equiv.sumCompl` constructions implement `d`; no cardinality or endpoint data are postulated.
- `vertexEquiv_splitSource`, `vertexEquiv_splitTarget`: exact source and target identities for the canonical vertex inclusion. `exteriorHasRight` proves every external edge has an endpoint in the right summand.
- `Radial.d`, `si`, `ti`, `so`, `xo`, `f`, `stratum`: the actual split of an indexed `NestedMetricGeometry.metricBox` induced by the open metric ball `dist o v < R` and its complement.
- `Radial.hend`, `hleft`, `hfar`: exact global simple-graph endpoints, left roots equal to the actual finite `innerBall hG o R`, and every right vertex at distance at least `R`.
- `Radial.mem_stratum_iff`: membership in the pulled-back `maximalSplitStratum` is exactly `Separated` for the actual exterior bits. `allClosed_mem_stratum` proves the conditioning event nonempty.
- `Radial.bad_stratum_subset_closedLocalEvent`: the actual maximal-stratum exceptional-set inclusion is proved using `OpenPathGeometry.bad_maximalSplit_subset_closedLocalEvent`.
- `Radial.cylinder_abs_sub_le_radial_farConnection_of_good`: for `R ≤ r ≤ n`, the actual metric-box finite-volume cylinder bound using the constructed radial stratum. The normalized common-upper `hgood` is the remaining explicit stochastic hypothesis; all geometric inputs are discharged by the construction.

## Exact scope and remaining obstruction

The radial certificate uses **the whole finite ball** `innerBall hG o R` as roots and the **same** `R` as arm radius. This is a genuine maximal-stratum/open-path estimate, but it is not the smaller-fixed-root, growing-radius bound needed for nonpercolation-vanishing arms or a full strong-uniqueness theorem. In particular, no hgood theorem, arm-vanishing theorem, DLR equality, or whole-paper result is claimed. The remaining common-upper `hgood` and the fixed-root/growing-radius geometric refinement are separate work.

## Verification

Run `bash check.sh` from this member directory. The script uses the installed Lean 4.35 toolchain, checks the single source with `warningAsError=true` and default heartbeats, saves `audit-output.txt`, and scans for forbidden declarations/placeholders and heartbeat overrides. The source's 13 printed principal audits contain only `propext`, `Classical.choice`, and `Quot.sound`. No dependency, toolchain, repository source, or unrelated member file is modified. The full repository check is not run by this member-local script.
