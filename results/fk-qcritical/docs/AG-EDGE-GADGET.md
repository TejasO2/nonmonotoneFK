# One-edge AG enhancement gadget

`FK/AGEdgeGadget.lean` constructs the elementary enhancement which opens an
edge when either its bond bit or its independent activation bit is open.
All 29 declarations are included in `Audit.lean`.

## Proved content

- `enhancedConfig` uses the actual separate `JointConfig` bond/activation
  coordinates and `enhancedEvent` pulls back the genuine bond event.
- `enhancedConfig_jointLaw` computes the exact normalized inhomogeneous
  marginal, whose rates are `orRate p s = p + (1-p)s`. No unnormalized toy
  product or activation-independent event is substituted.
- `bondToActivation` closes only the bond at one edge. The code proves the
  forced-configuration identity and that bond pivotality becomes activation
  pivotality for the enhanced event.
- `edgePivotal_event_mul_le` and `sum_edgePivotal_event_mul_le` prove
  `δ P(bond-pivot) ≤ 2 P(activation-pivot)` and the finite expected-pivot-count
  bound under explicit common two-value probability minorants.
- `enhancedEssential_of_onDoubleRay` supplies an actual activation-pivot witness
  at every edge on a genuine double ray. The packing results derive a
  bounded-distance essential set from local-cover and diameter inputs,
  including the genuine line-graph metric.

## Scope not claimed

This is a finite one-edge construction. Arbitrary bounded-range annular
implantation, deriving the geometric packing inputs from quasi-transitivity,
Margulis–Russo differential integration, finite-arm limits and the global AG
strict critical shift remain open. No Theorem 1.4, 1.8, 1.10 or 1.11 is
inferred.
