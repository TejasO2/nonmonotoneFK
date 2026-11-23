# Genuine simultaneous annular sleeves

## Result

`AGSleevedAnnulus.lean` constructs, for every simple graph `H`, a new simple graph
`FK.AGImplant.Sleeve.graph H` on `V ⊕ H.edgeSet`.

- The original vertices and bonds are retained.
- Every original bond receives a distinct midpoint and a genuine two-edge
  bypass between its endpoints.
- `baseEdge H` is injective. `leftSpoke H` and `rightSpoke H` are graph edges,
  not abstract path predicates.

For a finite set `S` of original bonds, `annulus H S` is its embedded bond set
and `support H S` is one shared-activation device opening the union of all the
two-edge bypasses. The construction has the following verified properties.

1. **Actual simultaneous replacement.** `annular_replacement` reconnects the
   endpoints of every bond in the annulus after all those ordinary bonds have
   been closed and the one device activated. Both orientations of a `Sym2`
   edge are handled. The replacement is an actual `OpenConnected` witness.
2. **Pivot conversion on infinite graphs.**
   `activationPivotal_openConnected_annulus` and
   `activationPivotal_deviceArmEvent_annulus` convert a selected original-bond
   pivot into an activation pivot for the actual open-connection and one-arm
   events. No `Fintype` assumption occurs in these geometric theorems.
3. **Exact finite-product comparisons.**
   `openConnected_annulus_edgePivotal_event_mul_le` and
   `deviceArmEvent_annulus_edgePivotal_event_mul_le` give
   `δ ^ S.card * P(bond pivot) ≤ (2 ^ S.card : ℕ) * P(activation pivot)`.
   The law is the normalized independent Bool product on separate bond and
   activation coordinates. The hypotheses are exactly a common lower bound
   `δ` on both values of every coordinate law; no homogeneity is assumed.
4. **Not support-contained surgery.** `disjoint_annulus_edges` proves the
   annulus and activated sleeve are disjoint. Thus these theorems do not follow
   from the existing support-contained special case. Also,
   `card_annulus : (annulus H S).card = S.card` and
   `card_edges_le : (edges H S).card ≤ 2 * S.card`.
5. **Actual infinite-graph structure.** `graphConnected` and
   `graphLocallyFinite` preserve connectedness and local finiteness.
   `automorphism` lifts every base graph automorphism, including midpoint
   membership. Under explicit vertex- and edge-transitivity of `H`, with nonempty
   vertices and edges, `graphQuasiTransitive_of_vertex_edge_transitive` proves
   quasi-transitivity by exhibiting the original-vertex and midpoint orbit
   classes.

## Direct import

The source has exactly one direct import:

```lean
import FK.AGDeviceEssentiality
```

That existing module supplies `FK.AGBoundedRangeImplant` and
`FK.FKQuasiTransitiveDevices` transitively. No shared source was copied or
edited; the new graph and sleeve construction are in this member directory.

## Scope and residuals

This is a concrete shared-activation enhancement on a constructed simple
graph. It is not a rerouting theorem for an arbitrary essential enhancement on
an arbitrary quasi-transitive graph.

The quasi-transitivity conclusion assumes both vertex- and edge-transitivity
of the base graph. It is not a theorem that sleeving preserves arbitrary
quasi-transitivity with no further hypothesis.

Remaining work toward an AG strict shift includes:

- the subsequent `AGUniformSleevePacking` module now constructs uniformly
  bounded, pairwise-disjoint whole templates under base edge-transitivity and
  a double-ray seed hypothesis, with exact finite-overlap accounting;
- summing pivot comparisons and deriving the differential inequality for the
  resulting multibond activation profile;
- integrating that inequality and passing through the infinite-volume
  reference-law argument.

None of those steps, an interior strict critical-point shift, or an infinite
product-probability comparison is claimed here. In particular, the finite
probability theorems deliberately require finite `graph H` edge sets, while
the deterministic pivot conversion is the part valid on infinite graphs.

The result is also unrelated to the previously rejected inhomogeneous
path/star discontinuity example: the new statements concern explicit bypass
surgery and exact pivot transport, not a discontinuous activation endpoint.

## Verification

`compile.sh` uses the repository Elan installation at `.scratch/elan`, forces
the pinned `leanprover/lean4:v4.35.0` toolchain, leaves heartbeats at Lean's
default, and builds only `AGSleevedAnnulus.olean` from its source.
`audit.sh` elaborates `AGSleevedAnnulusAudit.lean` against that olean through
Lake's pinned import environment.

The independent build passed. `AGSleevedAnnulusAudit.txt` records 13 exact
`#print axioms` reports for the principal declarations; every report contains
only:

```text
[propext, Classical.choice, Quot.sound]
```

A source scan found no `sorry`, `admit`, `unsafe`, new `axiom`, or heartbeat
override. No full-project build was run, to avoid competing with the
coordinator's integration check.
