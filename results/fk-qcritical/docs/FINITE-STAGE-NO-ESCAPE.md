# Positive association and no-mass-escape on genuine nested finite boxes

Public module: `FK.StageInstantiation`. This completes the analytic stage
instantiation for a **fixed-vertex nested edge family**, rather than merely
stating another interface. It does not construct the final geometric
far-connection event or most required limiting laws.

## Exact nested stage model

`FixedVertexFamily E V` has a finite vertex type $V$, endpoint maps src/tgt on
an arbitrary edge type $E$, and a monotone family of finite edge sets.
Every stage is a genuine `FiniteBox`, retaining loops and parallel labels and
use the same setoid boundary $\xi$ on the ambient vertex type.

The box law is the actual closed-exterior `finiteVolumeLaw`. Its
`interiorRestriction` cylinders satisfy the genuine pushforward identity:

$$
\operatorname{law}_B(\alpha)(\operatorname{interiorRestriction}^{-1}S)
 = \operatorname{FK}_{B,\alpha}(S).
$$

The nested stage injections are compatible with surface endpoints.
`fkMeasure_le_of_inj` therefore lifts the edge-domain comparison to genuine
stage measures: an increasing stage-$m$ event has mass at most that of its
lift at each later stage $k$.

## Positive association proved, not assumed

`posAssoc_of_fkPMF` uses the genuine normalized finite FKG result
`fkPMF_association_events` on $A$ and $D^c$ for increasing $A$ and decreasing
$D$. Indicator identities, singleton sum normalization and a probability split
give the exact `PosAssoc` shape used by edge-domain monotonicity.

At $p=0$ and $p=1$, the finite laws are proved to be Dirac masses at the all-
closed and all-open configurations. Those endpoint proofs, plus the all-open
restriction theorem at $p=1$, lead to `posAssoc_of_one_le` and
`finiteVolumeLaw_stage_mono_q_ge_one` at arbitrary boundary setoids.

## The no-escape result

For $q\ge1$, $0<p\le1$, any boundary setoid, an arbitrary limit point $\mu$ of
the actual stage laws, increasing stage events whose cylinder unions are
$C_\infty$, `noEscape_of_finiteVolumeLaw_stage_q_ge_one` proves

$$
\limsup_k \nu_k(C_k)\le\mu(C_\infty).
$$

Positivity-association and stage-monotonicity are conclusions here, not
axiomatized inputs. The merge with the separate isolated-vertex invariance is
available for other graph box models, but the present fixed-vertex class does
not need vertex changes.

This theorem still needs a genuine limiting law when that existence is an
obligation of the source argument. The essential remaining field is the actual
far-connection event/exhaustion. It does not discharge `hfin` of the full
one-point Gibbs passage, and no $q<1$ version follows from positive
association.

## Concrete instances and the explicit $q=1$ limit

`loopFamily` has genuine loop labels `0,…,n` at stage $n$.
`loopFamily_noEscape_q_ge_one` treats its increasing loop events and their
union. Moreover, `loopExhaustion` forms a genuine `BoxExhaustion`, and
`loopFamily_noEscape_unconditional` uses the previously proved $q=1$ limit to
give a fully unconditional no-escape statement for $0<p\le1$:

$$
\limsup_k\nu_k(C_k)
\le \operatorname{Bernoulli}(p)(\exists j\ge1:\omega_j=\mathrm{true}).
$$

`parallelFamily` uses two distinct endpoint vertices with parallel labels.
`parallelEvent_iff_connected` identifies the specified open-label event with
actual free-boundary edge connectivity by explicit open-walk analysis.
`parallelFamily_noEscape` then has the corresponding $q\ge1$ form at any limit
point.

For `onePoint_edge_of_noEscape`, the `openRate_identification` carrier identity
is proved as well. Its `hfin`, which identifies stage one-point conditionals
with a fixed box's conditional, remains separate.

## Verification

The exact source and separately extracted 33 declarations were independently
rebuilt under Lean 4.35/current imports/default heartbeats. All principal
axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
Run `./check.sh` for the complete release verification.
