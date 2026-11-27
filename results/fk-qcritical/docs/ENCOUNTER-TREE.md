# Finite encounter trees from actual three-way arms

Public module: `FK.EncounterTreeConstruction`.

This is a fixed-centre, fixed-scale geometric construction. It is not a global
Burton–Keane uniqueness proof and does not supply the multi-centre analytic
input by itself.

## Main result

For a connected graph `G`, a positive natural number `n`, y ∈ V and an actual
positive-scale `ThreeWayArms G ω y n` witness,
`nonempty_finiteThreeArmTree_of_threeWayArms` constructs a `Nonempty` package
containing:

- a finite `G.Subgraph` whose coe graph is genuinely a tree;
- a distinguished vertex equal to `y` of degree at least three;
- every degree-one vertex at graph distance exactly `n` from `y`;
- every retained vertex within the closed radius-`n` ball of `y`; and
- every retained edge open in `ω`.

The `Nonempty` wrapper is intentional: the arm witnesses existentially provide
the geometry, and eliminating that existential proposition into a `Type`
valuation is not needed. `nonempty_finiteThreeArmTree_of_allScales` applies the
constructor at a centre with three-way arms at every scale.

## Why this is an actual tree

Each path inducts to its **first** vertex outside the radius-`n` open ball.
Support before this exit remains inside the closed ball, its terminal point has
distance exactly `n`, and the whole truncated path remains simple, open and
contained in the original arm. Finiteness follows immediately from the finite
path supports.

Only the three traversed edge sets are used, not ambient edges between path
vertices. Ambient chords are therefore excluded by design. Support inclusion
preserves the pairwise arm separation outside the centre.

Two finite subgraph trees glued at exactly one vertex are proved connected and
their vertex/edge counts satisfy the exact tree identity. Applying that twice
forms the three-path tree; there is no appeal to planarity or a false
"connected implies acyclic" simplification.

Three distinct next-neighbours on the non-nil truncated paths exist at the
centre and prove its degree at least three. Every other nonterminal branch
vertex has degree at least two, so any degree-one vertex must be one of the
three sphere terminals.

## Finite sphere branch bound

`FiniteThreeArmTree.card_branch_le_card_boundary` directly applies the public
`TreeBranchBound.card_branch_le_card_boundary` to the set of tree vertices at
exactly radius `n` from `y`. `card_boundary_le_metricSphere` injects these
vertices into the fixed ambient finite sphere, whose `innerBall` is finite by
local finiteness. Thus
`card_branch_le_metricSphere` bounds the actual encounter tree's branch points
by the fixed metric sphere cardinal.

`mem_innerEdges_and_open_adj` additionally proves all retained edges are open
and belong to `innerEdges G y (n + 1)`, making the finite edge window explicit.
The total class is not a multi-centre forest, global marked-count bound,
Følner-sequence construction, law/event invariance argument or cluster-count
constancy theorem. It also does not address the exactly-two-cluster case, AG,
Eq9 or arbitrary-dominant uniqueness.

## Verification

The independent pinned Lean 4.35 clean rebuild checked the complete source and
bare-import audit, producing 11 reports for seven unique principal declarations.
All use only `propext`, `Classical.choice`, and `Quot.sound`.
There are no placeholders, custom axioms or option overrides. The public check
is `./check.sh` from `results/fk-qcritical`.
