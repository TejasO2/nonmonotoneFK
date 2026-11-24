# Covering reference comparison and spoke-pivot transport

Public module: `FK.AGCoveringReference`, with the main results in
`FK.AGImplant.Sleeve.CoveringReference`. All probability statements concern
normalized infinite independent products on the actual sleeved graph; no
random-cluster law is used.

## The covering hypothesis and exact endpoint profile

`CoveringBase S` requires every original bond to belong to some device. It is
stronger than positive density. In that class, with labelled-edge-uniqueness,
a common annulus size $R>0$, and comparison speed
$c=(\min(a,1-b))^R/(2^R R)$,

$$
P(\text{original}=p,\ \text{spokes}=p,\ \text{activation}=s)
 \le
P(\text{original}=p-cT,\ \text{spokes}=p,\ \text{activation}=s+T).
$$

The initial profile is genuinely uniform on original bonds and spokes. The
`threePoint` endpoint representation makes the unchanged spoke rate explicit;
it is not a uniform lower edge parameter.

The monotone curve is proved for arbitrary device index types, with no
cardinality bound. It uses the finite trace comparison and the decreasing
arm limit, not a derivative/limit interchange. `refMaxTime` gives the admissible
elapsed-time formula
$\min((p-a)/c,b-s)$.

For a positive starting percolation probability, the percolating original-bond
set is nonempty at the endpoint. Hence its infimum satisfies
$p_c^{\mathrm{orig}}\le p-cT<p$. This is a strict decrement of the critical
original-bond rate in the constructed sleeve model.

A concrete edge-unique instance indexes singleton annuli by every bond. It is
not a translated-template packing and is not any proof that positive density
holds in a quasi-transitive graph.

## Spoke-pivot transport

The naive claim that a spoke is at least as pivotal as its activation is false:
the spoke may be open while the activation is closed. The correct event closes
all spokes of that device, then varies its activation. The supplied ordering and
monotone transport lemmas prove this at the joint configuration level and for
finite arm events. Trace likelihood ratios bound the corresponding pivotal-event
weight. This is genuine support geometry for extending the line to spoke
coordinates; the extended line and integrated shift are not included.

## Residuals

Covering does not discharge the paper's positive-density essential-enhancement
hypothesis. No `p_c(H)` comparison is made, and no general uniform-spoke rate
statement is obtained. `exists_box_speed_lt` records that the box-dependent
speed is not uniform over all parameter boxes, so the present constants do not
supply AG integration over endpoints near 0 or 1.

Nothing here is an FK, DLR, or numbered-paper theorem. In particular it is not
`hAG`, Theorem 1.4, or strong uniqueness.

## Verification

Both main sections were independently rebuilt with the current public
`FK.InfinitePackedSleeves` import on pinned Lean 4.35. The 23 principal
declarations in `Audit.lean` use exactly `propext`, `Classical.choice`, and
`Quot.sound`. Default heartbeat limits are retained. `./check.sh` verifies the
complete integration.
