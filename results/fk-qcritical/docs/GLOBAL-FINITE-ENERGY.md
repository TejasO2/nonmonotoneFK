# Finite energy and global uniqueness before DLR

## Result

`GlobalFiniteEnergy.lean` closes the pre-DLR global-to-exterior-uniqueness gap
left by `NonlocalFiniteVolume.lean`, at interior parameters `0 < q` and
`0 < p < 1`, on a countable locally finite simple graph (local finiteness is
used by the downstream nonlocal geometry, not by the finite-energy estimate).

The following now compile:

- `aeAtMostOne_geometry_of_tendsto_of_globalAtMostOne`: a coherent finite-volume
  weak limit with an **arbitrary exterior configuration at each box** has
  `AEAtMostOne data.geometry μ` whenever it has global at-most-one-cluster
  uniqueness almost surely. No DLR fact for `μ` is assumed.
- `mem_gibbsMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne` and
  `mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne`: the
  corresponding source-Gibbs and arbitrary geometric target-DLR conclusions.
- `mem_dlrMeasures_of_tendsto_finiteVolumeLaw_of_globalAtMostOne`: the
  closed-exterior specialization.
- `aeAtMostOne_geometry_of_tendsto_dlr_of_globalAtMostOne` and
  `mem_dlrMeasures_of_tendsto_dlr_of_globalAtMostOne`: the same argument for an
  arbitrary weak limit of DLR laws on a fixed specification; no coherent
  finite-volume presentation of the approximants is required.

In the last theorem, the proof uses the new exterior-uniqueness result to apply
`NonlocalInterior.mem_dlrMeasures_of_tendsto_of_ae_eventually_eq` to obtain the
**source** DLR identity. Only after that does it call
`ConventionTransport.mem_dlrMeasures_of_atMostOne`. No global-to-exterior DLR
transport is used circularly.

## Proof

1. For a fixed finite labelled graph, `pointFloor` is the minimum normalized FK
   point mass over the finitely many boundary partitions and configurations.
   It is positive at interior edge parameters by `pointFloor_pos` and bounds
   every point mass by `coe_pointFloor_le_fkPMF`.
2. For one DLR law, `measure_map_closeBox_le_of_isDLR` proves
   `(closeBox B)_* μ ≤ (pointFloor B q p)⁻¹ • μ`. On each exterior fibre, the
   close-box preimage is empty unless the all-closed interior lies in the event;
   in that case the point-mass floor bounds the conditional mass of the event.
3. `measure_map_le_smul_of_tendsto` passes such a continuous-pushforward
   domination bound to an arbitrary weak limit. It uses bounded continuous
   tests, `HasOuterApproxClosed` on closed sets, and compact inner regularity to
   extend the conclusion to every Borel set. This is necessary because global
   uniqueness is not a cylinder event.
4. Consequently the close-box pushforward of the limit is absolutely continuous
   with respect to the limit. Global uniqueness therefore remains almost sure
   after closing each box (`ae_globalAtMostOne_closeInside_of_tendsto_of_isDLR`).
5. On `closeInside`, two infinite exterior components supply two infinite global
   components, so closed-box global uniqueness is exactly the input required by
   `AEAtMostOne data.geometry μ`. Coherence supplies the eventual DLR identity
   for every fixed smaller box along an arbitrary exterior sequence.

## Exact remaining restriction

This does **not** claim Proposition 1.8(2) for a sequence of wholly unrelated,
noncoherent boundary partitions `α n`. Such a sequence is not in general known
to satisfy DLR on each fixed smaller box for one fixed source specification, so
the nonlocal weak-closure theorem has no fixed source to which it applies.
Constructing and stabilizing that source specification remains a separate
combinatorial/Markov-factorization problem. The endpoint cases `p = 0` and
`p = 1` are also outside this interior finite-energy argument. No full
arbitrary-boundary or endpoint theorem is asserted.

## Verification

- The repository Elan installation selected Lean 4.35.0; compilations used
  default heartbeat settings and produced `.olean` files only in this member
  directory. No shared source or GitHub state was edited.
- `GlobalFiniteEnergy.log` records the independent compile. An earlier warning
  about a no-op `change` was removed before the final rebuild.
- `AuditGlobalFiniteEnergy.lean` audits 13 principal declarations. The final
  `AuditGlobalFiniteEnergy.log` reports exactly `propext`, `Classical.choice`,
  and `Quot.sound` for every declaration.
- Integration: place the module as `FK/GlobalFiniteEnergy.lean`, import it from
  `FK.lean`, and copy the principal `#print axioms` lines to the project audit.
