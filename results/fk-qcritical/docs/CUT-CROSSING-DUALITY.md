# Finite cut-graph crossing on the square lattice

Public module: `FK.CutCrossingDuality` (namespace
`FK.PlaneTopology.CutCrossing`). This proves a genuine finite dual-cut crossing,
not merely a list of parity or incidence interfaces.

## Model and hypotheses

Let $a:\mathbb Z^2\to\mathsf{Bool}$ encode an arbitrary vertex set. The vertices
of `cutGraph` are unit cells in a rectangular box, together with an outside
vertex below and one above it. Adjacency is by shared cut bonds, and the outside
vertices are adjacent to bottom/top cells exactly where there is a cut on the
respective wall.

Assume that the left wall is wholly in $a$ and the right wall is wholly outside
$a$, with at least one row of cells ($n>0$). No probabilities, random FK law, or
infinite-volume assumptions are used.

## Proved crossing

`degree_inr_zero` and `degree_inr_one` compute the outer degrees:
they equal the number of horizontal cut bonds on the bottom and top rows.
The proof uses explicit row-index bijections from `Finset.card_bij` and the
outer adjacency clauses. The Prop-valued form `hCutP` avoids rewriting the
Bool-valued indicator in a dependent proof field.

`odd_changes` makes both outer degrees odd because the left/right wall states
differ. Every interior cell has even degree: `adj_inl_iff` and
`sideNbr_injOn_cutSides` identify and distinguish its four cut-side neighbours,
hence `degree_inl_eq`, and numerical cut-side parity gives `even_degree_inl`.

The handshake lemma `reachable_of_odd_degree` therefore proves

$$
(\operatorname{cutGraph}).\operatorname{Reachable}
  (\mathrm{inr}\ 0)(\mathrm{inr}\ 1),
$$

i.e. `exists_cut_crossing`: a genuine dual-cut graph path from below to above.
This is not an assertion about fixed norm shells or an arbitrary matroidal dual.

`reachable_of_cut_le` carries this walk through any graph containing the cut
adjacency relation, by `SimpleGraph.Reachable.map`. The endpoint hom is identity
on vertices, so a graph of primal-**closed** bonds can be used on the same
underlying cut-graph type.

## Closed-bond successor and remaining scope

That transfer is instantiated by the successor
[finite primal/closed-bond duality](CLOSED-BOND-PRIMAL-DUALITY.md).
`FK.PrimalClosedDuality` constructs the closed-bond graph, chooses $a$ by open
left-reachability, proves that open paths cannot exit that set except across
closed bonds, and computes the corresponding `gridCrossEquiv` labels. Its
contrapositive produces a primal open left-to-right walk when the closed graph
has no below-to-above connection.

The converse crossing implication, `GlobalAtMostOne`, cofinal exhaustion,
general plane embedding, FK measure theory, and Theorem 1.11 remain outside
this module's claim.

This closing dual transfer used an API repair: the transfer proof was replaced
with `SimpleGraph.Reachable.map` using the `map_rel'` evidence field.
The independently validated version, not the earlier erroneous proof attempt,
is the public one. No mathematical premises or conclusions changed.

## Verification

The public file was independently rebuilt under Lean 4.35 against current
public imports. Its 20 fully qualified principal declarations are included in
`Audit.lean`; they depend only on `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, custom axiom, `unsafe`, `native_decide`, or
heartbeat/trust override is present. Run `./check.sh` for complete release
verification.
