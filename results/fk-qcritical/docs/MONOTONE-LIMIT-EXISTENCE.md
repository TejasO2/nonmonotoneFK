# Cylinder and monotone limiting-law existence

Public modules: `FK.MonotoneLimitExistence`, `FK.StageLawUpTBound` and
`FK.FixedVertexLimit`. These prove actual weak limits from cylinder convergence
and instantiate a narrow fixed-vertex nested-edge FK family. They do not yet
construct canonical growing-vertex free and wired limits.

## From upper corners to full weak convergence

`MonotoneLimitExistence` recovers the Boolean pattern mass `cyT S T` from the
upper-corner mass `upT S T` by subtracting all strict supersets. Downward
induction on the finite Boolean lattice then proves
`tendsto_cyT_of_tendsto_upT`: convergence of all upper-corner masses implies
convergence of every pattern mass. Finite disjoint patterns recover arbitrary
finite-coordinate cylinder masses.

A closed set is written as the decreasing intersection of the finite-coordinate
cylinders induced by its restrictions along an enumeration of the coordinate
type. Continuity from above and the closed-set Portmanteau criterion therefore
prove `tendsto_of_tendsto_cyl` and `tendsto_of_tendsto_upT`.

For `exists_isFKLimit_of_tendsto_upT`, compactness supplies a subsequential
weak limit. Clopen convergence identifies that limit's upper-corner masses
with the prescribed limits, after which the preceding generic theorem gives
convergence of the entire genuine `finiteVolumeLaw` schedule. It is not merely
a subsequential-existence statement. Monotone and eventually monotone corner
masses have real limits, yielding `exists_isFKLimit_of_mono_upT` and its
eventually monotone version for a genuine `BoxExhaustion`.

## Fixed finite vertices, nested edge labels

For `NoEscape.FixedVertexFamily`, `StageLawUpTBound` lifts an upper-corner event
to the genuine graph interior and invokes the previously verified normalized
finite-FK edge-injection comparison. At $q\ge1$ and interior $p$, the mass of
each fixed upper corner is monotone once all its coordinates are present.

`FixedVertexLimit` composes this with the generic existence theorem. It yields
a genuine full-sequence `IsFKLimit` for a covering nested-edge family on one
finite vertex type, with any fixed boundary setoid, including the free/discrete
boundary. Infinite edge types can occur by adding loops or parallel labels;
this is not a growing-vertex simple-graph exhaustion.

## Delimitations

No source-boundary wired convention is constructed. In particular, the top
setoid on the box's entire vertex type is not the paper's wired-at-infinity
boundary and is not presented as $\phi^1$. No canonicality, uniqueness or DLR
result follows from existence alone.

For growing vertex boxes, one still needs the actual restriction/mixture
identity: the larger free law restricted to the smaller coordinates is a
mixture of smaller-box laws with induced exterior connectivity. FKG would then
compare every fibre with the smaller free law. Presenting that coherence as a
hypothesis is not a proof of it, so this remains open.

All three exact sources were independently rebuilt at default heartbeats with
Lean 4.35.0. An expanded audit of 31 principal declarations reports only
`propext`, `Classical.choice` and `Quot.sound`.
