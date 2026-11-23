# Local stabilization for noncoherent FK specifications

## Proved result and exact scope

`NoncoherentStabilization.lean` adds a varying-specification weak-closure mechanism for actual FK DLR equations. It does **not** finish fixed-source DLR membership for every arbitrary `IsFKLimit`, and it does not repeat the close-box or `AEAtMostOne` results in `NoncoherentFiniteEnergy`.

The new predicate

```lean
LocallyStabilizes l μ α β
```

says that for `μ`-almost every `x`, there is a neighbourhood `U` of `x` such that, eventually in the filter index `i`, `α i` and `β` agree on all of `U`. This is stronger than pointwise convergence and is deliberately separate from almost-everywhere local constancy of the reference `β`.

The main declarations are:

1. `tendsto_measure_disagreement`: joint local stabilization forces the approximating measures of the disagreement sets to zero. The proof chooses a measurable full-measure good set, approximates it from within by a compact set, takes a finite open subcover with a common eventual stabilization statement, and bounds the remaining mass using the closed-set Portmanteau inequality. The potentially nonmeasurable disagreement sets are only estimated by closed supersets.
2. `tendsto_of_le_add_of_le_add`: two-sided additive errors tending to zero imply convergence in `ℝ≥0∞`, using the zero-perturbation liminf/limsup identities.
3. `tendsto_lintegral_indexed_of_tendsto_of_locallyStabilizes`: a lower-integral limit theorem for genuinely varying finite-valued indices. The reference integral uses the existing fixed-index theorem; both error directions are bounded by the disagreement mass. Local constancy of `β` is an explicit separate input.
4. `isDLR_of_tendsto_of_locallyStabilizes`: varying-source DLR closure for an actual finite box. The proof tests every Boolean cylinder, uses `extendExterior` for the finite exterior coordinates, transports the actual conditional FK masses through the varying-index theorem, and concludes equality with the reference FK reconstruction. The approximants need not share a `BoundaryConvention`; they need only satisfy DLR for their own explicitly supplied local specifications.
5. `mem_dlrMeasures_of_tendsto_of_locallyStabilizes`: the same statement for all boxes of an exhaustion.
6. `ae_eventually_eq_of_geometric_atMostOne` and `mem_dlrMeasures_of_tendsto_of_locallyStabilizes_of_atMostOne` discharge reference local constancy for geometric assignments from exterior at-most-one uniqueness.
7. `mem_dlrMeasures_of_isFKLimit_of_locallyStabilizes_of_globalAtMostOne` is the exact scoped arbitrary-`IsFKLimit` corollary: global uniqueness supplies the already integrated noncoherent exterior-uniqueness result, while induced local DLR data and `LocallyStabilizes` remain explicit hypotheses at every box.
8. `exists_strictMono_tendsto_pi` and `exists_strictMono_eventually_eq_pi`: simultaneous pointwise diagonalization for a countable dependent product of finite discrete types, with a genuine strict subsequence.
9. `tendsto_finiteVolumeLaw_subseq`: convergence of the actual composed finite-volume laws along a strict subsequence of an `IsFKLimit`. Boxes and boundary setoids are both reindexed; this is not mislabelled as `IsFKLimit` on the original exhaustion.
10. `exists_boundary_denseProbe_subsequence`: simultaneous exact pointwise stabilization along the countable dense probe sequences of every box exterior.

All these results are stated at general `0 < q` and `p ≤ 1` where their hypotheses allow it. No endpoint degeneration is hidden.

## Residual hypotheses and the unrestricted obstruction

The arbitrary noncoherent-boundary proof is not complete. Moreover,
`NoncoherentCounterexample` proves the unqualified claim false: the constant
fully wired one-edge limit has global/exterior uniqueness but no geometric
DLR class. The following are therefore real required hypotheses for a valid
restricted argument, not merely bookkeeping to finish an unconditional result:

- For an arbitrary `IsFKLimit` boundary sequence, the module does not yet construct the induced local boundary assignments or prove their local DLR compatibility on every fixed smaller box.
- Dense-probe diagonalization constructs a pointwise limit only on the specified countable probes. Full exterior configuration spaces are generally uncountable and not first-countable, so this is not a subsequential compactness theorem on all exterior assignments.
- Neither diagonal pointwise convergence nor the existing `AEAtMostOne` conclusion supplies `LocallyStabilizes` on a common neighbourhood. That joint local stabilization remains an explicit input to the closure theorem.
- The geometric corollary `mem_dlrMeasures_of_isFKLimit_of_locallyStabilizes_of_globalAtMostOne` discharges the reference's local constancy from global at-most-one uniqueness via `NoncoherentFiniteEnergy.aeAtMostOne_geometry_of_isFKLimit` and `NonlocalInterior.eventually_partition_eq_of_atMostOne`. Its `hDLR` and `hstab` inputs are exactly the remaining noncoherent obligations, not the fixed-source conclusion itself.
- No full Theorem 1.4/1.9/1.10/1.11, coherent-wrapper replacement, or fixed-source noncoherent completion is asserted.

## Verification

Run `./build_and_audit.sh` in this member directory. It uses the existing Lean 4.35.0 toolchain, does not install or change tools, performs one-target Lean checks with default heartbeat settings, builds the module `NoncoherentStabilization`, then checks `AuditNoncoherentStabilization.lean` against that built module. No shared result file is written.

`BuildNoncoherentStabilization.log` is the module check. `AuditNoncoherentStabilization.log` contains twelve exact `#print axioms` checks; every principal declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. The script also rejects `sorry`, `admit`, `unsafe`, and custom `axiom` declarations in the new source. A whole-repository build was not run.
