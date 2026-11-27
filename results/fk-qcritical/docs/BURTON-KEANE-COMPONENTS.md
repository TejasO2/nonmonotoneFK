# Burton–Keane: positive encounters and analytic/tree interfaces

Public modules: `TreeJunction`, `LeafJunction`, `BurtonKeaneGeometry`,
`LeafWalk`, `BurtonKeaneWeak`, `LeafArms`, `ExternalClusters`,
`IncidenceGeometry`, `IncidenceAttachment`, `ExternalRoot`, `InternalGeometry`,
`AssemblyBranch`, `ConnectedSupport`, `TripleAssembly`, `PatchLifting`,
`EncounterProbability`, `FolnerFirstMoment`, `TreeBranchBound`, and
`EncounterTreeBound`.

This is a substantial **component library**, not a proof of Burton–Keane
uniqueness, Theorem 1.11, or the paper's global planar argument.

## Actual finite encounter and open patching

`exists_threeWayArms_openInternal_of_three_infinite` begins with three actual
infinite open clusters, represented by three roots with infinite open connected
components and all three pairwise nonconnection hypotheses. On a connected
locally finite graph it produces a finite vertex set `U` and a centre `y` such
that, after opening precisely the actual graph edges internal to `U`, the centre
has three open simple arms at every metric scale, meeting pairwise only there.

The construction chooses finite connected support for the roots, preserves the
original-root attachments, keeps separated exterior components away from all
incident edges of the support, and splices them at a central tree junction.
External walks may contain their own attachment point. The interface handles
this exception explicitly rather than imposing inconsistent exclusion of every
central vertex. The inherited double-patch glue was repaired by proving
`openInternal_idem`, together with `openInternal_eq_updateFinset` on the finite
actual internal-edge support.

All-scales `ThreeWayArms` and `EncounterEvent` are measurable on countable
graphs: the proofs expand countable endpoints/walks, finite vertex sets,
centres, and the scale intersection. `exists_internalPatch_mem_encounterEvent`
expresses the encounter as a fixed finite coordinate update preserving every
external coordinate.

## Insertion tolerance and positive mass

`FinitePatternInsertionTolerance μ` requires that every positive-measure
exterior event depending off a finite patch support retain positive measure when
that finite pattern is forced. This is an explicit measure hypothesis, not an
implicit property of every FK law.

`measure_pos_of_forall_exists_patch_of_finitePatternInsertionTolerance` uses a
countable patch enumeration to select one patch from a positive cover and then
applies insertion tolerance. Consequently,
`measure_pos_encounterEvent_of_three_infinite_of_insertionTolerant` gives
`0 < μ (EncounterEvent G)` whenever `0 < μ {ω | ThreeInfiniteClusters G ω}`.
Interior Bernoulli percolation has this property from independence and
positivity of each finite Boolean cylinder; both forced values and the empty
support case are included.

No independence, group invariance or probability normalization is hidden in
the general measure-level hypothesis. The Bernoulli specialization is proved,
but the corresponding property for the paper's FK/Potts measures is not derived
here. Scalar `p = 0` or `p = 1` is excluded from the Bernoulli version.

## Analytic and finite-tree components

`FolnerFirstMoment` proves exact finite-window first moments for marked events.
Under a configurationwise bound `markedCount A F ω ≤ b`, a uniform lower bound
`c ≤ μ (A v)` gives `F.card * c ≤ b` in `ℝ≥0∞` and, along a nonempty
`F n`, `c ≤ b n / |F n|`. A vanishing `b n / |F n|` limit forces `c = 0`.

`HomogeneousEvents` records the actual input: each `shift v` preserves the
measure and pulls `event v` back to the root event. This does not build a group
action, ergodicity or Følner sequence. A finite collection of quasi-transitive
orbit representatives could instead use the uniform lower-bound form directly,
once supplied for the actual invariant law and event.

`card_branch_add_two_le_card_leaf` proves, by finite-tree degree sums,

$$|\{\text{branch points}\}|+2 \leq |\{\text{leaves}\}|.$$

Thus branch points are bounded by any set containing all leaves.
`markedCount_le_of_encounterTree` applies this to a supplied encounter tree with
leaves in a boundary set `B` and every marked centre of degree at least three.
It does not construct or prune that tree.

## Remaining mathematical work

1. Derive `FinitePatternInsertionTolerance` for the relevant actual FK/Potts
   measures from conditional specifications; interior parameters are relevant
   and the paper's basis-law finite energy must not be assumed for free.
2. Build a finite encounter tree with leaves on the window boundary and every
   encounter centre of degree at least three, including its pruning argument.
3. Derive genuine law/event invariance (or the finite-orbit uniform mass bound),
   an explicit Følner sequence, and the vanishing boundary/window ratio.
4. Establish cluster-count constancy or an alternative deduction. Ruling out at
   least three infinite clusters does not exclude **exactly two**. A merging of
   two infinite components requires the appropriate insertion tolerance and a
   contradiction to finite positive count; none is proved here. Infinitely many
   clusters, on the other hand, directly imply positive probability of three.
5. Join these inputs into a model-specific Burton–Keane at-most-one-cluster
   statement. Such an invariant amenable statement would be distinct from the
   paper's planar conclusion and would not prove general AG, Eq9, Theorem 5.1,
   or Theorem 1.11.

Reference to ordinary tails proves only zero/one existence of some infinite
cluster, not constancy of the full cluster count; the two are not conflated.

## Verification

The independent clean rebuild elaborated all 16 encounter/dependency modules
plus the consolidated audit with pinned Lean 4.35/default heartbeats, and all
76 printed axiom reports were standard-three. The analytic/tree package was
independently rebuilt separately with 11 principal reports, likewise clean.
The public `Audit.lean` has 34 distinct principal entries covering those two
scopes. No `sorry`, `admit`, `unsafe`, `native_decide`, custom axiom, or option
override is used; stale inherited olean artifacts were not trusted.
