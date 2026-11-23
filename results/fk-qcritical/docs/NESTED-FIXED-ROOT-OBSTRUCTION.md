# Fixed-root obstruction for whole-ball radial splits

## One crossing edge is enough

`GeneralObstruction.lean` defines a configuration with exactly one selected open
box edge and proves its exact glued form and all possible open-connected pairs.
If that edge is external but touches the radial ball, it violates `Separated`,
so the configuration is outside the actual maximal split stratum. Any vertex in
the split that is not an endpoint of this edge can connect only to itself.

`not_badRootAttachment_of_leftEdge` therefore contradicts bad-only attachment
with roots of radius $L$ when a disjoint split vertex has distance greater than
$L$. This is a genuine bad-configuration obstruction, not an all-configuration
root demand. The theorem's ingredient is explicit: it does not assert existence
of a suitable edge and far vertex for every graph.

## Exact path statement

`FixedRootObstruction.lean` instantiates this geometry on the semi-infinite path
using only the edge from $R-1$ to $R$. For $2\le R\le r$, bad-only attachment
for the radial split at radius $R$ forces a root at $R-1$ or $R$. If every root
has distance at most $L$ from the centre, then

$$R\le L+1.$$

The same conclusion is proved directly in the
`metricNestedEquiv`/`maximalSplitStratum` form used by
`NestedBadRootArmVanishing`. The smaller box radius in that application grows,
so no one finite root set supplies all its split presentations. Conversely,
choosing all roots in the open ball of radius $R$ satisfies attachment for every
configuration trivially; this positive fact does not supply fixed small roots.

## Mathematical scope

The paper's Theorem 5.1 uses a random increasing sequence of connected
$S_n(\omega_3)$ with closed exterior boundary. The fixed whole-ball split cannot
implement that requirement with fixed roots. The needed explored/random
stopping-region construction, its `hgood` identity, and Theorem 1.9 remain open.
These modules give no negative assertion about that random-region argument or
about the general theorem on arbitrary graphs.

## Verification

Both exact sources were independently rebuilt with pinned Lean 4.35.0/default
heartbeats. The seven path-module and four general-module principal audits
passed the repository's allowed-axiom checker, using only the three standard
Lean axioms. No placeholders, custom axioms, unsafe declarations, or elaboration
overrides occur. The public release check repeats all audits.
