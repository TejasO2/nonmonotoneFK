# Bounded-range route and annular implants

## What is formalized

`AGBoundedRangeImplant.lean` introduces `FK.AGImplant.deviceConfig`. Its joint
configuration has separate bond and activation coordinates. An enhanced bond
`e` is open exactly when its ordinary bond is open or some active device has
`e` in its support. Thus one activation may open a whole finite route; this is
not the independent one-activation-per-edge OR model of `FK.AGEdgeGadget`.
`deviceConfig_force_activation_outside` proves that toggling a device changes
nothing outside its support.

The local modification `implantClose e` closes only the pivotal bond. Given a
walk `route` joining that bond's endpoints and contained in one device's
support, `activationPivotal_openConnected_implantClose` converts a bond pivot
for an actual `OpenConnected` event into an activation pivot. The analogous
`activationPivotal_deviceArmEvent_implantClose` uses the repository's actual
`armEvent`. `activationPivotal_walkDevice_openConnected` specializes the
support to `OpenPath.walkEdgeFinset route`; the remainder of a cycle is an
immediate instance, although cyclicity itself is not needed for walk surgery.

The proof is deliberately asymmetric. With activation off, the modified
configuration is below the original bond-closed enhanced configuration, so
the original pivot obstruction applies. No auxiliary edge is opened in this
branch. With activation on, `openConnected_replaceEdge` replaces every
traversal of the original bond by the implanted route, in either orientation.

## Finite annuli and exact probability ratios

`annularClose R` closes every ordinary bond in a finite set `R`. The local
geometric input to `activationPivotal_openConnected_annularClose` is:

- the distinguished pivot bond belongs to `R`; and
- for every source-open enhanced edge `s(x,y)` in `R`, the configuration after
annular closure and activation has an actual open walk from `x` to `y`.

Outside `R`, source-open enhanced edges are preserved automatically. With
activation off, annular closure is below the original bond-closed enhanced
configuration. `openConnected_surgery` combines the supplied local walks into
the required global open connection. This is a per-edge walk interface, not a
hypothesis asserting the desired global pivot conversion.

For arbitrary normalized finite Bool laws on bonds and activations, with a
common lower bound `δ` on both values of every coordinate law, the following
are proved using the existing independent-product transport:

- `openConnected_edgePivotal_event_mul_le` and
  `deviceArmEvent_edgePivotal_event_mul_le`:
  `δ * P(edge pivot) ≤ 2 * P(activation pivot)`;
- `openConnected_annular_edgePivotal_event_mul_le` and
  `deviceArmEvent_annular_edgePivotal_event_mul_le`:
  `δ ^ R.card * P(edge pivot) ≤ (2 ^ R.card : ℕ) * P(activation pivot)`.

The constants come respectively from one changed joint coordinate and from
all bond coordinates in `R`. The measure is the actual normalized
`OpenPath.FinProb.pi (Sum.elim bond activation)`; no replacement product law
is postulated.

## Precise remaining hypotheses and geometric blocker

This is not a proof of the arbitrary-essential-enhancement AG theorem. The
remaining work is:

1. Identify the intended star/cycle decrement profiles with an appropriate
   local activation rule, or prove the corresponding stochastic comparison.
   The file proves the route-device model above, not that identification.
2. Construct the annular replacement walks. For a single cycle device, an
   auxiliary walk joining the head's endpoints suffices. A general annulus
   requires simultaneous replacement of all source-open edges removed there;
   separated device packing and essentiality alone do not construct these
   disjoint sleeves.
3. Sum over pivots/devices with finite overlap, integrate the resulting
   differential inequality, and pass to the infinite-volume percolation
   function. None of those steps is asserted here.

The annular geometry is a genuine issue, not only a Lean engineering gap.
Balister–Bollobás–Riordan, *Essential enhancements revisited*
([arXiv:1402.0834](https://arxiv.org/abs/1402.0834)), explains that the
original lattice annular rerouting figure is not valid in general and isolates
the required two-path rerouting condition. That source is not a counterexample
to the route theorem here; it explains why an arbitrary quasi-transitive
instance still needs a graph-geometric proof rather than a formal packing
argument alone.

## Verification

The module and audit were checked in the member directory with the repository
Elan and pinned `leanprover/lean4:v4.35.0`, using default heartbeats and Lake's
computed import path. `AGBoundedRangeImplantAudit.txt` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for all 17 principal/helper
declarations. No shared-results file was edited and no full-project check was
run; verification here is the targeted module build and exact axiom audit.
