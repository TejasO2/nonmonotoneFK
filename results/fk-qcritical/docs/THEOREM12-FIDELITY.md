# Theorem 1.2 finite-comparison reliability audit

## Verdict and scope

I compared the current `FK/Theorem12Less.lean` and `FK/Theorem12Greater.lean`
with Beffara–Faipeur–Oke, arXiv:2512.16486v1, especially Theorem 1.2 (paper
pp. 4–5), Propositions 3.1–3.2 (p. 15), and their proofs (pp. 16–19).
Primary source: <https://arxiv.org/html/2512.16486v1>.

**No genuine mathematical statement error was found in the two final audited
declarations.** They have the correct stochastic directions, rates, graph
conditions, strict witnesses, and actual normalized finite FK law. The audit
also confirmed that their final signatures have no supplied stationary law,
ordered joint sequence, convergence statement, clock law, or auxiliary
schedule. This is not an audit of the infinite-volume Proposition 4.2 or of
Theorems 1.4, 1.10, or 1.11.

The checked source hashes were:

- `Theorem12Less.lean`: `e1d71f7bb44c9f8000bb3e54d9b72a000ea801913b7ff14885bf0d11f5516c80`
- `Theorem12Greater.lean`: `965a7e13144997d586b223c8738aaffa1f3a5b5b070e154e32e26e35402a8145`
- `CanonicalDynamics.lean`: `ea1ba81251f2b048c46ea83b89c89c2ec3697d661ab7212db55ee77234638a88`

## Exact final declarations

The entry points are

- `FK.EnhancedComparisons.theorem_1_2_of_lt_one`;
- `FK.EnhancedComparisons.theorem_1_2_of_one_lt_q`.

Their mathematical inputs are a finite `LabelledMultigraph`, an arbitrary
boundary setoid `ξ`, interior `0 < p < 1`, positive `q` in the stated side of
`1`, and the three geometric predicates `WiredConnected`,
`TwoWiredVertices`, and `¬ IsWiredForest`. These respectively express
connectedness after wiring, at least two quotient vertices, and existence of
an alternate route (hence failure of the wired forest condition). This is the
connected, non-tree, at-least-two-vertices-after-wiring scope of the paper,
represented directly for labelled multigraphs rather than simplified away.

For `q < 1`, the lower comparison is closed-cutset enhanced and the upper
comparison open-path enhanced. For `q > 1`, the lower comparison is open-path
enhanced and the upper comparison closed-cutset enhanced. Both return nonempty
enhancement data and a strictly positive local enhancement. The path data
include `HasEnhancingPaths` and an actual endpoint-connection statement for
every certificate. The strict path witness is constructed from `hnotforest`;
the strict cutset witness comes from connectedness plus two wired vertices.
The needed `Nonempty G.Edge` instance is then obtained from that cutset edge.

## Rate and orientation fidelity

`FKEnhancement.StochasticallyDominates μ ν` means `μ A ≤ ν A` on measurable
increasing events, so the second measure dominates the first. The four final
inequalities therefore have the intended orientation.

For `p < p'` (the `q < 1` branch):

- `lowerEnhancedRate` is `p + extendedCutsetEpsilon`;
- `upperProductParameters` is `p' - upperEpsilon`.

For `p' < p` (the `q > 1` branch):

- `lowerProductParameters` is `p' + lowerEpsilon`;
- `upperEnhancedRate` is `p - extendedCutsetEpsilon`.

`cutsetWeight` evaluates the closed-certificate probability at `max p p'`.
The upper path bonus evaluates the open-path probability at `p`, and the lower
path bonus at `p'`; these are respectively the minimum-rate evaluations in the
two branches. Thus the enhancements are exactly the paper's
`|p'-p| P_max(cutset closed)` and `|p'-p| P_min(path open)` profiles.

The proposed `Theorem12Fidelity.lean` makes the raw real-valued enhancement
families, their `[0,1]` bounds, non-identical vanishing, and all four profile
identities available as the following compiling declarations:

- `FK.EnhancedComparisons.Fidelity.normalized_lower_cutset_profile`;
- `FK.EnhancedComparisons.Fidelity.normalized_upper_cutset_profile`;
- `FK.EnhancedComparisons.Fidelity.normalized_upper_path_profile`;
- `FK.EnhancedComparisons.Fidelity.normalized_lower_path_profile`.

These are interface lemmas only. They do not assume or prove an additional
stochastic comparison, and they are not alternative statements of the whole
paper theorem. Applied to the data returned by the two final declarations,
they expose precisely the `min(p,p')+ε` and `max(p,p')-ε'` notation used in the
source. No theorem-level hypotheses were discharged by these normalization
wrappers; the point is that none were hidden.

## Certificates, adapters, and normalization

- A cutset certificate is expressed using the actual
  `endpointsConnectedWithout` predicate and must avoid the distinguished and
  enhanced edges as required. The cutset used for strictness is the explicit
  `otherEdges` certificate at a non-self-loop after wiring.
- `HasEnhancingPaths` requires every candidate path to avoid its distinguished
  edge and use only auxiliary edges, and requires a nonempty collection. The
  separate `hpath` conclusion in the final theorems identifies openness of a
  certificate with endpoint connection in the actual wired labelled graph.
- `OpenPath.configToBool` sends bit `1` to Boolean `true`, preserves order, and
  is used in the final measured path laws. The FK law is not silently
  identified with a bit-valued law: the PMF is mapped explicitly.
- `G.fkMeasure` is definitionally `(G.fkPMF …).toMeasure`, with `fkPMF` given
  by normalization of the actual FK weights. Cutset products are `Measure.pi`
  of `Ber(true,false,r e)` and have an `IsProbabilityMeasure` instance. Path
  products come from normalized finite `FinProb`/`PMF` objects, whose open bit
  has mass `r e`.

## Clocks and schedules

The final theorems call canonical wrappers, not conditional reduction
wrappers. `CanonicalDynamics.uniformClock` assigns every edge mass
`1 / Fintype.card E`, proved positive for nonempty finite `E`.
`auxiliaryList enhanced` is `enhancedᶜ.toList`, with duplicate-freeness and
exact complement specification; `completeSchedule E` contains every edge.
Consequently no positivity-of-clock, full-schedule, or enumeration hypothesis
remains in the final statements.

As documented by the project, these proofs use a discrete-time Glauber jump
skeleton. This is enough for the stationary-product and convergence argument
formalized here, but is not a construction of the paper's continuous-time
exponential-clock trajectories.

## Kernel checks

Using the repository Elan at `.scratch/elan`, Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Lake 5.0.0, both target
source modules elaborated independently with `lake env lean`. The audit source
is `Theorem12Audit.lean`. As a final stale-object guard, copies of the exact
`Theorem12Less` and `Theorem12Greater` source files were elaborated with their
own `#print axioms` commands appended. Both final declarations reported only:

```
[propext, Classical.choice, Quot.sound]
```

The four canonical comparison inputs reported the same set:

- `FKEnhancement.graphConnectionEvent_lower_comparison_canonical`;
- `FKEnhancement.graphConnectionEvent_upper_comparison_canonical`;
- `FKEnhancement.CanonicalDynamics.graphConnectionEvent_upper_path_comparison_canonical`;
- `OpenPath.LowerPathCoupling.lower_path_comparison_of_one_lt_q_canonical`.

All four new fidelity declarations also reported only that same standard set.
Logs are in `.scratch/final-less-axioms.txt`,
`.scratch/final-greater-axioms.txt`, `.scratch/final-canonical-axioms.txt`,
and `.scratch/final-fidelity-audit.txt`. Fresh canonical elaboration emitted
four pre-existing style-linter suggestions about `letI`, and no errors. A
token scan found no `sorry`/`admit`/`unsafe`/`axiom` in the target or proposed
modules. This is a kernel audit, not a substitute for the source comparison
above.

I did not run the full repository `check.sh` or its all-project build/audit
matrix; the checks reported here are the independently elaborated target
modules and their final/canonical declarations.

## Reliability notes, not counterexamples

1. Older generic files still expose conditional limiting-dynamics wrappers.
   They must not be confused with the four unconditional actual-graph
   declarations listed above. `docs/MODULES.md` retains generic wording that
   `Proposition32` has conditional whole-comparison inputs; that describes the
   older wrapper layer, not these new entry points.
2. Earlier in this run the shared proof-status documentation briefly described
   Theorem 1.2 and Proposition 3.2 as incomplete. It was updated externally
   during the run. The current `docs/PROOF-STATUS.md` correctly marks them
   proved, so this is not a current defect.
3. The branchwise final statements emphasize enhancement sets, certificates,
   and local positive witnesses rather than displaying two raw epsilon
   families in one conjunction. The new fidelity interfaces close this
   presentational gap without changing the mathematical claims.
4. No error in arXiv:2512.16486v1 is asserted by this audit.
