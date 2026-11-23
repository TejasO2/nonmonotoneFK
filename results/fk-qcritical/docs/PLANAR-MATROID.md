# General labelled graphic duality and finite Euler

Deliverable: `PlanarMatroid.lean`. It compiles independently with the repository's
Elan installation, Lean 4.35.0, and the pinned Mathlib. It does not modify any
shared file under `results/`.

## What is actually constructed

For the repository's `FK.Finite.LabelledMultigraph`, arbitrary finite vertex and
edge types are retained, as are loops, parallel labels, isolated vertices, and
the labelled open-edge weight. `setConfig` and `openEdgeSet` convert exact sets
of labels to and from Bool configurations; `openCard` is exactly the set's
`ncard`.

The primitive graph notion remains the existing one: an open forest is a labelled
configuration in which deleting any open labelled edge disconnects that edge's
ends. No simple-graph quotient is formed.

The main graph results are:

* `card_vertices_le_componentCount_add_openCard` and
  `isOpenForest_iff_componentCount_add_openCard`:
  `components(omega)+openCard(omega) >= |V|`, with equality iff `omega` is an
  open forest. The proof opens/closes one edge at a time and uses the repository's
  exact component-update theorems.
* `cycleMatroid`, with simplification theorem `cycleMatroid_indep`: the actual
  open-forest sets form a finite matroid. For the augmentation axiom, if no edge
  of `J \ I` can be added to a forest `I`, then `I` has the reachability relation
  of `I union J`. Hence
  `components(I)=components(I union J) <= components(J)`.
  Together with the two forest identities this contradicts `I.ncard < J.ncard`.
  The proof does not incorrectly assume `I subset J`.
* `reachable_setConfig_iff_of_isBasis` and
  `componentCount_setConfig_of_isBasis`: a matroid basis of an edge set has the
  same reachability relation and actual component count as that set. An edge
  whose addition is dependent has its ends connected in the basis.
* `cycleMatroid_eRk_add_componentCount`: for every configuration,
  `eRk(open omega) + components(omega) = |V|`, in `ENat`.

## Plane/dual data and the Euler theorem

`LabelledDualPair` contains a primal labelled multigraph and a face-vertex
labelled multigraph on the *same actual edge-label type*. `P.Face` is meaningful
face data for a plane application; it is not an anonymous component-count
function.

`GraphicDualCertificate` has exactly three fields:

1. `(P.primal.cycleMatroid)✶ = P.faceDual.cycleMatroid`;
2. `Nonempty P.Face`;
3. the all-open face-dual connection graph is preconnected.

This is a combinatorial Whitney/graphic-duality certificate. It does **not**
contain the desired all-configuration Euler identity as a hypothesis.

`componentCount_dual_add_card_vertices` proves, for every Bool configuration,

```
componentsDual(complement omega) + |V|
  = componentsPrimal(omega) + 1 + openCard(omega).
```

Mathematically, put `X=open(omega)`, `X^c=closed(omega)`, `M=cycleMatroid primal`.
The proof combines

```
eRk(M,X) + componentsPrimal(omega) = |V|,
eRk(M*,X^c) + componentsDual(complement omega) = |F|,
eRk(M*,X^c) + eRank(M) = eRk(M,X) + |X^c|,
eRank(M) + eRank(M*) = |E|,
eRank(M*) + 1 = |F|.
```

The second display is transported along the graphic-dual equality. The last
uses actual dual all-open connectivity and includes isolated-face bookkeeping.
Natural-number arithmetic then gives the component identity. No analyticity or
probability argument is involved.

`euler_allOpen` is the possibly disconnected Euler formula, and
`euler_allOpen_of_preconnected` gives `|F|+|V|=|E|+2` under a nonempty,
preconnected all-open primal hypothesis.

## Actual finite FK duality: what disappears

`actual_fkPMF_graphicDual_duality` instantiates the existing
`actual_fkPMF_duality` with `Equiv.refl P.Edge`. Its former pointwise geometric
input

```
forall omega, componentsDual(dual omega) + |V|
  = componentsPrimal(omega) + 1 + openCard omega
```

is now proved by `componentCount_dual_add_card_vertices`. The theorem retains
the actual normalized FK PMFs, free boundary connection graphs, labelled edge
products, `Bool` complement duality, and the existing dual-parameter
normalization. It requires `0<q` and `0<p<1`, exactly as the existing interface.

The graphic-dual equality and dual all-open connectivity do **not** disappear:
they are the precise remaining geometric input. A continuous plane embedding,
rotation system, or other source of planar geometry still has to construct the
face-dual labelled multigraph and establish those facts.

## Scope and verification

This does not claim a strict critical shift, whole Theorem 1.11, a general
infinite-volume limit, or dual nonpercolation implying uniqueness of a primal
infinite cluster. No infinite-cluster transport is supplied here. It is the
finite labelled matroid/Euler component of direction G.

Independent check used (paths abbreviated):

```
lake env lean .../m5/PlanarMatroid.lean
```

It exited 0 with no output. `PlanarMatroid.audit.txt` records `#print axioms`
for ten key declarations. Every one reports exactly the usual axioms
`propext`, `Classical.choice`, and `Quot.sound`; there are no new axioms,
placeholders, `sorry`, `admit`, or `unsafe` declarations.
