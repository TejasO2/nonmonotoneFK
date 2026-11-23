# Endpoint completion for global finite-energy weak limits

## Proved result

`EndpointGlobalFiniteEnergy.lean` supplies the endpoint bridge missing from
`GlobalFiniteEnergy` and combines it with that module's interior-rate results.
All results require `0 < q`; no result extends `q` to an endpoint.

### New endpoint lemmas (not case-split restatements)

For a countable configuration type and **arbitrary** functions `α n` and
`η n`, with no coherence assumption, the following are proved:

- `conditionalLawLimit_apply_open_zero` and
  `conditionalLawLimit_apply_closed_one`: the coordinate cylinder mass of a
  conditional-law weak limit vanishes as soon as the exhaustion contains the
  coordinate.
- `eq_closedLaw_of_tendsto_conditionalLaw_zero` and
  `eq_openLaw_of_tendsto_conditionalLaw_one`: an arbitrary-exterior
  conditional-law weak limit at `p = 0` or `p = 1` is respectively the actual
  all-closed or all-open point mass. The varying exterior is not assumed fixed
  or closed.
- `mem_dlrMeasures_zero_of_tendsto_conditionalLaw` and
  `mem_dlrMeasures_one_of_tendsto_conditionalLaw`: those limits belong to every
  target DLR class. No source convention, geometric compatibility, or global
  uniqueness is needed in these standalone endpoint statements.
- `eq_closedLaw_of_tendsto_dlr_zero` and `eq_openLaw_of_tendsto_dlr_one`: a
  weak limit over an arbitrary nontrivial filter of DLR laws on one fixed
  specification is the corresponding deterministic endpoint law.
- `mem_dlrMeasures_zero_of_tendsto_dlr` and
  `mem_dlrMeasures_one_of_tendsto_dlr`: the resulting exact endpoint weak
  closure for an arbitrary target assignment.

The conditional-law argument uses the exact finite-box laws
`conditionalLaw_zero_apply_open` and `conditionalLaw_one_apply_closed`, the
clopen coordinate cylinders, and `exh.eventually_mem`. The DLR argument uses
the existing exact singleton classifications and uniqueness of limits. It does
**not** apply `pointFloor_pos` at an endpoint.

### All-rate completion on a simple graph

The following now hold at every `p ≤ 1` on a countable locally finite simple
graph:

- `mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one`:
  arbitrary-exterior coherent weak-limit transport to a target DLR class.
- `mem_gibbsMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one`:
  the corresponding target-convention Gibbs statement.
- `mem_dlrMeasures_of_tendsto_finiteVolumeLaw_of_globalAtMostOne_of_le_one`:
  closed-exterior specialization, without source local constancy.
- `mem_dlrMeasures_of_tendsto_dlr_of_globalAtMostOne_of_le_one`: weak closure
  for an arbitrary nontrivial filter of DLR laws on a fixed specification.

The `0 < p < 1` branches call the newly accepted finite-energy theorems
unchanged. Their coherent source, geometric source/target compatibility,
local finiteness, and almost-sure `GlobalAtMostOne` hypotheses are therefore
retained. At `p = 0` and `p = 1`, the branch uses the exact deterministic
endpoint bridges above, and those extra hypotheses are genuinely unnecessary.

## Imports and provenance

- `GlobalFiniteEnergy.lean` in this member directory is a byte-for-byte copy of
  `.ultramath/smwsu3cov/m2/GlobalFiniteEnergy.lean` (SHA-256
  `eefe5676a16951fc2ca6a38c2f25deeb78c34dd24315c7c8c7bddc054b7275a9`).
  It was independently rebuilt here and has not been edited.
- The public module imports the integrated `FK.GlobalFiniteEnergy` and
  `FK.InteriorEndpointNormalization`. The latter supplies the existing exact
  endpoint DLR classifications through `FK.ConventionEndpoints` and
  `FK.EndpointIntegration`. Only the worker-local import was changed for
  release; the mathematical source is unchanged.

## Verification

Using the repository Elan installation and pinned Lean `4.35.0`, with default
heartbeats and one source target per invocation:

- `GlobalFiniteEnergy.lean` compiled independently to a member-local `.olean`.
- `EndpointGlobalFiniteEnergy.lean` compiled to a member-local `.olean` with an
  empty diagnostic log.
- `AuditEndpointGlobalFiniteEnergy.lean` elaborated all 14 principal
  declarations. `AuditEndpointGlobalFiniteEnergy.log` reports exactly
  `propext`, `Classical.choice`, and `Quot.sound` for every one.
- The new source and audit contain no `sorry`, `admit`, `unsafe`, or new
  `axiom` declaration. No shared result, dependency, toolchain, or GitHub state
  was edited.

## Explicit residuals

- This does not derive a fixed-source interior weak closure for unrelated,
  noncoherent boundary sequences; direction A remains separate.
- It does not assert a standalone all-rate `AEAtMostOne` or
  global-to-exterior-uniqueness theorem. The all-rate conclusions here are the
  arbitrary-exterior Gibbs/DLR transport and fixed-specification DLR closure.
- It does not remove coherence, geometry, local finiteness, or global
  uniqueness from the interior branches of the all-rate statements.
- It proves no non-endpoint finite-energy estimate and no full named-paper
  theorem beyond these precisely scoped weak-limit statements.
