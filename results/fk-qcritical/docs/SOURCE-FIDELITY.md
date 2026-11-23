# Independent source-fidelity and trust review

Checkpoint reviewed: `664530aa1924a7dfeb2161d26b178522efb48a1e`.
Primary source: Beffara–Faipeur–Oke, arXiv:2512.16486v1,
<https://arxiv.org/abs/2512.16486v1>.  The v1 TeX source used for this review is
in `paper/main.tex`.  The six reviewed public files are
`results/fk-qcritical/FK/{InteriorWeakLimit,Proposition42Interior,WeakLimitCylinderTransport,AGEdgeGadget,ThetaDuality,PlaneCutCircuit}.lean`;
their exact hashes are in `target-hashes.txt`.

## Verdict

No hidden `sorry`, replacement probability model, or conclusion-facing axiom was
found in the reviewed declarations.  The statements are scoped mostly as their
documentation says.  They do **not** prove the whole of Proposition 1.8,
Theorem 1.4, or Theorem 1.11. At this reviewed checkpoint, Proposition 4.2's
active weak-limit package was still absent; it has since been supplied by
`FK/FKWeakLimitActiveDevices.lean`.
One unnecessary restriction was found and repaired locally: the final
`InteriorWeakLimit` transport required `0 < p < 1`, while its imported endpoint
API already proves the needed geometric transport for every `p ≤ 1`.

The new file `InteriorEndpointNormalization.lean` contains the compiling
all-rate corollaries

- `FK.InfiniteVolume.InteriorWeakLimit.mem_dlrMeasures_of_tendsto_of_globalAtMostOne_of_le_one`;
- `FK.InfiniteVolume.InteriorWeakLimit.mem_dlrMeasures_wired_of_tendsto_of_globalAtMostOne_of_le_one`.

They retain the actual locally constant coherent source convention, its
canonical closed-exterior finite-volume weak limit, geometric source/target
assignments, and almost-sure `GlobalAtMostOne`.  Thus this is an endpoint
normalization, **not** a proof of arbitrary interior weak-limit closure.

## 1. `InteriorWeakLimit`: Proposition 1.8(2), scoped

Source comparison: `paper/main.tex`, especially Proposition 1.8 at lines
282–288 and its Gibbs/limit discussion at lines 237–291.

### What is actually proved

- `FiniteBox.isDLR_iff_eq_reconstruct` identifies a box DLR law with
  reconstruction from its exterior marginal and the actual finite FK kernel.
- `FiniteBox.tendsto_reconstruct` uses weak convergence and a supplied
  continuity theorem for the conditional global FK specification.
- `FiniteBox.continuous_conditionalLaw_of_isLocallyConstant` proves that
  continuity when every boundary-partition map is locally constant.  The proof
  varies the exterior configuration and uses dominated convergence against the
  actual finite normalized FK measure; it does not freeze the exterior.
- `mem_gibbsMeasures_of_tendsto_finiteVolumeLaw_of_isLocallyConstant` takes a
  `BoundaryConvention`, its `compatible` nesting field, and a genuine weak
  limit of `finiteVolumeLaw` with closed exterior.  For each fixed small box,
  compatibility is used eventually along the exhaustion.
- The final source/target transport additionally needs geometric assignments
  on an actual countable simple graph and an almost-sure global
  at-most-one-infinite-cluster statement.

### Residuals

The theorem does not cover an arbitrary sequence `αₙ` in `IsFKLimit`, an
arbitrary sequence of boxes, or a nonlocally constant interior specification.
Canonical free/wired-at-infinity partitions involve nonlocal connection and
infinite-cluster events and are not shown locally constant.  Measurability and
compactness alone do not discharge this analytic step.  The source convention
must be coherent; arbitrary finite-volume boundary sequences need not have the
used nesting compatibility.  Nothing here proves Proposition 1.8(1), Choquet
assembly, extremality, or strong uniqueness.

The public target-transport statements used `hp₀ : 0 < p` and `hp₁ : p < 1`.
That restriction was not intrinsic: the two new corollaries above replace it by
`hp : p ≤ 1` and call
`ConventionTransport.mem_dlrMeasures_of_globalAtMostOne_of_le_one` after the
same source-Gibbs argument.  No other hypothesis was removed.

## 2. `Proposition42Interior`: active-device DLR case

Source comparison: Proposition 4.2 at `paper/main.tex` lines 723–747.

The two entry points are
`FK.EnhancedTransport.lt_dlr_sandwich_of_active_devices_interior` and
`gt_dlr_sandwich_of_active_devices_interior`.

### Binders and orientation

Each takes a fixed `BoxExhaustion`, one measurable `BoundaryAssignment`, and a
law in its actual `DLRMeasures`; parameters are interior `0 < p < 1` with
`0 < q < 1` or `1 < q`.  The strict sign of `p' - p` is derived internally from
`q`, not assumed as an extra comparison result.

For each star/cycle family the caller supplies:

- `IsSeparatedDeviceFamily`: the distinguished edge belongs to its device and
  every other device edge avoids the enhanced set;
- eventual finite-volume admissibility and complete-device activation;
- a nonempty-edge hypothesis for every box;
- for stars, an actual auxiliary closed cutset of cardinality at most `Δ - 1`;
- for cycles, actual auxiliary paths, the endpoint-connection semantics, and a
  certificate of cardinality at most `L - 1`.

The conclusion is correctly oriented despite the repository's argument order:
`StochasticallyDominates μ lower` means `μ` dominates `lower`, and
`StochasticallyDominates upper μ` means `upper` dominates `μ`.
For `q < 1`, the profiles are respectively `p + ε̂` on the star set and
`p' - ε̃` on the cycle set.  For `q > 1`, they are `p' + ε̃` on the cycle set
and `p - ε̂` on the star set.  Away from those sets they retain `p` and `p'`.
The definitions of `starEpsilon` and `cycleEpsilon` are exactly

```
|p'-p| * (1 - max p p')^(Δ-1),
|p'-p| * min p p'^(L-1).
```

Finite domination, rate estimates, cylinder convergence of the active Bernoulli
profiles, and the sign calculation are not conclusion-facing hypotheses.

### Residuals

This is the DLR case, not an `IsFKLimit` theorem.  Geometric star/cycle devices
have not been constructed from quasi-transitivity here.  The fixed exhaustion
and one assignment model the repository's DLR class; the paper phrases its
conclusion for the union of all FK weak-limit and Gibbs measures, so an assembly
step is still required before writing “for every FK measure.”  Nonempty boxes
at every index are retained.  No AG strict shift follows.

## 3. `WeakLimitCylinderTransport`: exact-rate, not active-packaged

Source comparison: the limit passage at `paper/main.tex` lines 735–747.

The file first proves lower/upper cylinder and full stochastic transport from
`IsFKLimit`, eventual exact cylinder equality of finite and limiting Bernoulli
profiles, and box-local finite domination.  It then proves the four entry
points

- `fkLimit_lower_cutset_comparison_of_rate_bound`;
- `fkLimit_upper_cutset_comparison_of_rate_bound`;
- `fkLimit_upper_path_comparison_of_rate_bound`;
- `fkLimit_lower_path_comparison_of_rate_bound`.

These use the actual `IsFKLimit` weak topology and the actual finite normalized
FK measure.  Weak convergence on a coordinate-supported clopen event is used,
rather than an unjustified equality of global measures on arbitrary boundary
events.  The final stochastic inequalities are on the genuine infinite
configuration space.

### Residuals

The four rate-exact declarations still take arbitrary scale-dependent enhanced
sets/profiles, exact coordinatewise enhanced-rate bounds, eventual
finite-cylinder profile equality, nonempty boxes, and (where applicable) path
semantics.  They do not internally form the active star/cycle families or
derive their eventual admissibility.  Consequently the active-device
weak-limit sandwich required a separate assembly, now supplied by
`FK/FKWeakLimitActiveDevices.lean`.
Parameters are interior and branch-specific; no endpoint or `q = 1` comparison
is claimed.  These are substantive rate-transport theorems, not wrappers whose
premise is the desired infinite-volume domination.

## 4. `AGEdgeGadget`: exact one-edge component only

Source comparison: the use of essential enhancements at `paper/main.tex`
lines 751–768.  The paper cites Aizenman–Grimmett for the general theorem; it
does not state this one-edge Lean gadget as a separate proposition.  This
review therefore checks the implemented semantics against the paper's stated
use, not a complete proof of the cited AG theorem.

`enhancedConfig` takes the OR of separate bond and activation coordinates.
`enhancedConfig_jointLaw` maps the actual finite independent joint product to
the independent Bernoulli product with exact rates
`orRate p s = p + (1-p)s`; `enhancedEvent_jointLaw` transports every event,
not only an increasing or one-arm event.  The laws are normalized finite
`FinProb` objects.

`activationPivotal_bondToActivation` provides the local pivot witness.
`edgePivotal_event_mul_le` and its sum prove
`δ P(bond-pivot) ≤ 2 P(activation-pivot)` under the explicitly stated common
two-value mass minorant for every bond/activation coordinate.  No probability
minorant is silently manufactured.

`enhancedEssential_of_onDoubleRay` constructs an activation-pivot configuration
for the actual open-double-ray event whenever the edge lies on a supplied
`DoubleRay`.  The two packing theorems output bounded-distance sets of such
essential activations.  The line-graph version uses the genuine connected
line-graph distance, so the density conclusion cannot be made trivial by a
zero metric.

### Residuals

The inputs still include local device cover, support diameters, devices whose
pivots lie on double rays, and (in the abstract metric version) a triangle law.
Quasi-transitivity and uniform bounded cycles/double rays are not converted
into these inputs here.  Arbitrary bounded-range annular implantation,
differential integration, finite-arm limits, and the global strict critical
shift remain absent.  The theorem names and documentation do not claim them.

## 5. `ThetaDuality`: special labelled families, not embeddings

Source comparison: the finite plane-duality setup at `paper/main.tex` lines
799–832 and the remaining needs of Theorem 1.11.

`cyclePair` and `parallelPair` retain the common labelled edge type.  For an
`IsLabelledCycle`, independent sets are proved to be proper subsets, bases to
be complements of singletons, and the two-face parallel dual's independent
sets and bases are computed from component counts.  The central theorem
`cycle_dual_cycleMatroid` is therefore an actual matroid equality, not an
assumption.  `graphicDualCertificate_cycle` and
`graphicDualCertificate_parallel` additionally prove nonempty faces and
all-open dual connectivity.  The one-loop and two-edge examples are explicit.

`IsLabelledCycle` is itself a graph-theoretic cycle certificate: nonempty
vertices, edge/vertex cardinal equality, all-open preconnectedness, and the
open-forest property after any non-all-open configuration.  Loops and parallel
labels are deliberately supported.

### Residuals

There is no arbitrary plane embedding, face incidence construction, general
theta graph, Whitney theorem, or Jordan-curve statement.  The module's
certificates are combinatorial inputs suitable for `PlanarMatroid`; existence
of such a certificate for a general plane graph is separate.  No infinite FK
uniqueness claim is made by these declarations.

## 6. `PlaneCutCircuit`: finite matroid interface only

Source comparison: the finite dual conditioning at `paper/main.tex` lines
820–832 and the dual-nonpercolation implication used at lines 841–856.

For a `LabelledDualPair` with a `GraphicDualCertificate`,
`exists_isCocircuit_subset_vertexCut` constructs a primal cocircuit through a
chosen edge of a vertex cut and contained in it.  Matroid duality gives
`exists_faceDual_isCircuit_subset_vertexCut`.
`OpenComponentSaturated` states precisely that no primal open edge crosses the
vertex-set boundary.  The dual-open interface theorem proves every circuit
label is primal closed, hence open in `dualConfig`.  The canonical open
component version also supplies reachability after deleting any one circuit
label.

This is faithful finite cut/circuit combinatorics, including loops and parallel
labels.  A supplied matroid-dual certificate is necessary for the arbitrary
pair; planar topology is not secretly inferred from the edge/vertex maps.

### Residuals

A matroid circuit is not identified with a Jordan curve.  There is no plane
drawing, embedded Jordan separation, finite-box exhaustion to infinity,
dual-nonpercolation argument, probability integration, or conclusion that the
primal has at most/exactly one infinite cluster.  These remain genuine steps
toward Theorem 1.11 and are not discharged by the existential finite circuit.

## Kernel and reproducibility checks

Using the repository Elan at `.scratch/elan` and Lean 4.35.0, with default
heartbeats and independent `lake env lean` invocations:

- `FidelityAudit.lean` elaborated 44 principal public declarations;
- `InteriorEndpointNormalization.lean` elaborated both new declarations;
- all 46 `#print axioms` reports contain exactly the standard set
  `[propext, Classical.choice, Quot.sound]`;
- a targeted token scan of the six public sources and the two new Lean files
  found no `sorry`, `admit`, `unsafe`, or `axiom` declaration.

The checks were performed one Lean process at a time. The public release audit
now re-elaborates the same public declarations and both new corollaries through
`Audit.lean` and the full `check.sh`; no conclusion-facing nonstandard axiom is
present. Kernel axiom reports establish trust in the elaborated statements,
not the source-fidelity conclusions documented above.
Kernel axiom reports establish trust in the elaborated statements, not the
source-fidelity conclusions documented above.
