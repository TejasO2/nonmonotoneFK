# Infinite planar dual uniqueness — status

## Proved

`InfiniteOpenCircuitUniqueness.lean` is a standalone Lean 4.35 development,
checked against public checkpoint `5196dd38a5b06e0ad4b3b079a8ba460578584ecd`.
It adds no declarations to the shared result tree.

The main results are:

- `OpenPathRealization.mem_ball_or_exists_vertexOnLabels_of_walk`: an exact
  walk induction. Before an open realized walk reaches a crossing-controlled
  label, its endpoints stay inside the sphere. Once such a label is reached,
  its near endpoint is connected to the walk source by the actual open prefix.
- `OpenPathRealization.exists_vertexOnLabels_of_openConnected_inside_outside`:
  the inside/outside specialization, using the existing metric-sphere
  intermediate-value theorem.
- `openConnected_of_two_infinite_of_sphericalOpenCircuit`: two infinite open
  components rooted inside a controlled sphere join whenever the label set is
  open and all its incident vertices are connected by paths **using only its
  own labels**. Finite properness of the vertex preimage supplies outside
  vertices in both components.
- `globalAtMostOne_of_openCircuitExhaustion`: a cofinal concentric exhaustion by
  these circuits proves the repository's actual `GlobalAtMostOne G ω`.
- `dualNonpercolationForcesPrimalAtMostOne_of_circuitConstruction`: packages the
  preceding result against the exact unproved target in `PlaneClusterTarget`.

Only `propext`, `Classical.choice`, and `Quot.sound` occur in the five axiom
audits. Run `./check.sh`; it uses default heartbeats, compiles one principal
module, and mechanically checks the audit and forbidden-placeholder syntax.

## Exact residual

This is **not** a proof of the full `DualNonpercolationForcesPrimalAtMostOne`.
The remaining hypothesis `hconstruct` requires a construction, from dual
nonpercolation, of cofinal **primal-open** spherical circuits with:

1. actual crossing control for every primal edge arc meeting the sphere;
2. every embedded vertex off the sphere;
3. all circuit labels open;
4. open-connectedness using only circuit labels; and
5. finite embedded-vertex preimages of balls (kept separately as `hproper`).

The expected finite-dual route is to apply cut/circuit duality with primal and
dual exchanged: finite dual-open components have primal-open boundary circuits.
The public `EmbeddedCircuitSeparation` instead produces **dual-open closed-in-
the-primal** circuits and has a root-inside implication for finiteness. It does
not supply the above cofinal exhaustion. Its finite `LabelledMultigraph` types
also cannot be silently used as an infinite graph exhaustion.

In particular, this development does not assert that dual nonpercolation alone
implies its own `HasOpenCircuitExhaustion`, does not call the finite theorem an
infinite theorem, and does not claim Theorems 1.4/1.9/1.10/1.11.
