# Finite dual-open components to primal-open spherical circuits

## Compiled results

`PrimalOpenBoundary.lean` imports the current public
`FK.InfiniteOpenCircuitUniqueness` and adds no axioms or placeholders.

1. **Circuit-carrier connectivity.**
   `LabelledMultigraph.reachable_of_cycleMatroid_isCircuit` proves that every
   two vertices incident to a cycle-matroid circuit are reachable using only
   circuit labels. The proof takes the connectivity class of one label,
   restricts a deleted-label path to that class, and uses minimal dependence to
   show that the class is the entire circuit. It handles loops and parallel
   labels.
2. **Reversed finite cut/circuit duality.**
   For every boundary edge of an actual finite **dual-open** component,
   `exists_primalOpen_circuit_boundary_dualOpenComponent` constructs a
   **primal-open** circuit contained in that boundary. All its incident
   vertices are genuinely connected in the primal configuration.
3. **Exact simple-graph carrier.**
   For a nonloop primal labelled multigraph, `simpleConfig` forgets parallel
   multiplicity by taking a simple edge open when some representative is open.
   `openConnected_simple_of_reachable_setConfig` transports walks while keeping
   every underlying edge in the image of the circuit. Consequently
   `openLabelConnected_simple_of_cycleMatroid_isCircuit` proves the repository's
   actual `OpenLabelConnected`, not merely labelwise openness or unrestricted
   ambient reachability.
4. **Actual spherical construction.**
   `SphericalPrimalCircuitGeometry` records only the independent metric/Jordan
   input (radius positivity, vertices off the sphere, and crossing control) for
   primal circuits on an actual `OpenPathRealization` of the simple graph.
   `sphericalOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary`
   turns every primal circuit contained in a finite dual-open component
   boundary into the existing `SphericalOpenCircuit` structure.
   `exists_sphericalOpenCircuit_boundary_dualOpenComponent` combines this with
   the existence theorem in (2), including a prescribed boundary edge.
5. **Cofinal interface composition.**
   `hasOpenCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries` constructs
   the existing `HasOpenCircuitExhaustion` from an explicitly cofinal supply of
   such circuits with a common centre.
   `globalAtMostOne_of_cofinal_dualOpenComponentBoundaries` composes that result
   with the already integrated `globalAtMostOne_of_openCircuitExhaustion` and a
   finite-preimage/properness hypothesis.

## Exact residual

This does **not** claim the general
`DualNonpercolationForcesPrimalAtMostOne`. The input data must still be
constructed for an infinite plane-dual pair:

- an exhaustion by finite labelled plane-dual boxes compatible with the global
  primal/dual configurations and the prescribed global edge equivalence;
- for every radius, a finite dual-open component having a primal boundary
  circuit with the same fixed centre and larger radius. Global dual
  nonpercolation makes global dual components finite, but this repository does
  not yet supply the finite-box translation or the Jordan argument selecting an
  enclosing boundary circuit;
- finite embedded-vertex preimages of balls, retained separately as `hproper`.

Also, `simpleConfig` deliberately quotients parallel primal labels. A full
application to a specified simple-graph edge equivalence needs faithful local
representatives (for example, no parallel labels in the boxes) or a separate
proof that this collapse commutes with the global dual configuration map. No
such compatibility is silently assumed.

Thus the remaining geometric/stochastic blocker is entirely the infinite
cofinal finite-box/Jordan assembly and its exact configuration transport; the
finite reversed cut/circuit and open-connected-carrier steps are proved.

## Verification

Run `./check.sh` from the project directory. It uses the pinned Lean 4.35
toolchain and default heartbeats, builds the public `FK` import root, and audits
nine public declarations from this module. The independent pre-integration build
reported only `propext`, `Classical.choice`, and `Quot.sound` for all nine. The
project script also checks the forbidden `axiom`/`unsafe`/`sorry`/`admit` syntax
and the complete audit's axiom set mechanically.
