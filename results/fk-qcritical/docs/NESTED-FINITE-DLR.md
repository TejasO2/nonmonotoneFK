# Nested finite specifications and moving clopen rates

Public modules: `FK.NestedTransportGeneral`, `FK.NestedFiniteDLR`,
`FK.GrowingFamilyDLR` and `FK.MovingClopenRate`. These are exact finite
specification/transport results and conditional limiting laws, not a complete
Proposition 1.8(2), Lemma 2.1 or Theorem 5.1.

## Exact nested DLR theorem

`FK.NestedFinDLR.isDLR_conditionalLaw_nested` takes a genuine `NestedBox B C`
between arbitrary finite labelled boxes and a boundary partition `α` on the
larger box. It shows that the large FK conditional law satisfies the small
box's DLR equation with `inducedBoundary`: the exterior-induced partition of
`α`, transported along the exact nested vertex equivalence.

The proof constructs the exterior fibre PMF and a nested mixture over the
induced boundary partitions. `map_fibrePMF_bind_subBox` proves that this
mixture is exactly the original FK law, including arbitrary boundary
partitions, adaptively nested regions and iterated labels. General transport
identifies component counts, partition functions and pointwise FK masses,
so arbitrary boundaries are not silently replaced by free ones.
`isDLR_finiteVolumeLaw_nested` specializes to the closed-exterior finite-volume
law.

## Growing families

For a `GrowingFamily`, `inducedAssignments` records the induced boundary
assignment assigned by the large-box boundary schedule. Outside the nested
range its value is a benign free default. Using the exact nested DLR theorem,
`eventually_isDLR_finiteVolumeLaw_growingFamily` supplies every small-box
finite-stage DLR equation needed for a subsequent weak-limit argument.

`mem_dlrMeasures_of_isFKLimit_growingFamily_of_locallyStabilizes_of_globalAtMostOne`
concludes DLR membership along the true box exhaustion from those equations.


The **joint local stabilization** of the induced assignments and global
at-most-one-cluster hypothesis remain explicit. This is not the paper's
unrestricted noncoherent implication, and it does not assert stabilization
merely from finite nesting. A source/fixed convention can be coherent along
useful sequences, but arbitrary boundary schedules still require an analytic
argument.

## Moving rates

`MovingClopenRate` proves that two-valued local rates converge whenever the
corresponding connection events stabilize in the large-box limit. The proof
uses nondecreasing finite clopen connections, continuity, the event union,
a vanishing escape-tail bound and weak convergence—not abstract monotone
rate identities alone. `onePoint_edge_of_clopen_escape` and
`isDLR_of_clopen_escape_moving` specialize this to one-edge edge-conditional inequalities
and global DLR membership. Their stage-local rate identities and conditional
law/source-geometric requirements remain explicit.

## Derived finite-stage one-edge rates

`DLROnePoint` proves that a global DLR law in a finite box has exactly the
`HasOnePointConditionalsBif` identities of its specification. The proof glues
the exterior composition and applies the ordinary finite off-edge FK
conditional identity at every exterior configuration. `onePoint_twoValuedRate_of_isDLR`
rewrites this as the `twoValuedRate` on the induced specification connection
event, rather than introducing another limiting-rate hypothesis.

`GrowingFamilyDLR.onePoint_twoValuedRate_growingFamily` applies these equations
between every nested pair of a growing family, at arbitrary outer boundary
assignments. Finite nested DLR consequently supplies the one-edge renewal
identity required by the moving-rate constructions, replacing the previous
`hfin` placeholder.

`MovingDominatedRate` computes moving two-valued rates from stochastic
domination together with vanishing escape tails. Both
`openBit_eq_limitRate_of_dominated_escape` and
`isDLR_of_dominated_escape_moving` retain the genuine dominating law and tail
criterion, plus the limit-rate identification needed for an actual box
specification. Their use still requires geometric arm/escape control and the
stabilization appropriate to a particular family.

## Eventual basal containment

`openBit_eq_limitRate_of_dominated_escape_eventual` and
`isDLR_of_dominated_escape_eventual_moving` strengthen the preceding dominance
result by asking the lower-event inclusion and escape inclusion only
**eventually** along the large-box index. This is the form in which genuine
finite nested data becomes available after a fixed finite region has entered
the large box, not an arbitrary boundary-set weakening. The total escape-tail
mass and the original bounded continuous tests still control the limiting
rate; all other FK and measurability requirements remain explicit.
