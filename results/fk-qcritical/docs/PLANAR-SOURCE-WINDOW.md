# Enhanced profiles and dual source-window assembly

Public modules: `FK.DualEnhancedProfiles`, `FK.SourceLowerWindow`,
`FK.PlanarSourceAssembly`, and `FK.DualSourceSingleton`.

This package carries out the parameter/product and source-measure steps of
Section 5.2. It is a **conditional assembly**, not full Theorem 1.11.

## Exact enhanced-profile duality

`one_sub_lowerWeightsReal_eq_upperWeightsReal_dual_of_q_le_one` and its
`one_le_q` companion prove the identity

$$1-\operatorname{lowerWeightsReal}(E_b,E_e,n,m,p,q)
  =\operatorname{upperWeightsReal}(E_e,E_b,m,n,p^*,q),$$

where $p^*=1-p'$. It includes the two equality regimes and uses the exact
cutset/path formulas, complementary minimum/maximum identities, and exchanged
star/cycle sets and exponents. Unit-interval versions transport the same
identity through an arbitrary edge equivalence. This is profile algebra, not a
construction of geometric dual devices.

## Every source FK law has the exact lower dominant

`SourceLowerWindow` defines `lowerLaw` and identifies it with Prop 4.2's actual
lower product. In both regimes, the enhanced lower product is stochastically
dominated by **every member of `SourceFKMeasures`**, over arbitrary induced
vertex exhaustions:

- weak limits are reindexed on a tail of their own exhaustion;
- geometric all-region DLR laws are restricted to any chosen exhaustion whose
  tail has nonempty edge boxes.

`map_dual_lowerLaw_q_lt_one` and `map_dual_lowerLaw_one_lt_q` identify the
actual complemented lower product with the exchanged upper product at the dual
parameter. No extra final DLR-class hypothesis is used by these comparison
lemmas.

## Conditional cluster and dual singleton windows

`PlanarSourceAssembly` applies a primal AG activation shift and dual AG
deactivation shift. Given the named deterministic
`DualNonpercolationForcesPrimalAtMostOne` geometry, it proves an almost-sure
exactly-one-infinite-cluster window for every primal source FK law, for `q<1`
and `1<q`. The enhanced parameters are explicit; the primal and dual radii are
separate.

`DualSourceSingleton` uses an `ExchangedDevices` compatibility record to feed
matched upper profiles into `SourceWindow`. Given that record, dual AG
deactivation and literal nested equation (9), it returns the actual dual
`SourceFKMeasures` singleton and its nonpercolation in the paper's original
parameter condition $\min(p,p')>1-p_c(G^*)-\gamma$.

## Remaining obligations, without being hidden in wrapper names

1. General AG and essential enhancement remain hypotheses.
2. Literal dual nested equation (9) remains a hypothesis. It is not replaced
   by the still-open ordinary nested prerequisite.
3. `ExchangedDevices` checks supplied device data. It does not construct dual
   stars/cycles, dual essentialness or a planar graph package.
4. The deterministic primal at-most-one geometry remains an input. Cofinal
   continuous/cellular windows are still required by the new sealed-cut route.
5. The final primal all-box step still needs `hfreeDual`, the relevant dual-box
   DLR class's singleton, a separate membership bridge into the dual source
   family, and primal all-box/source compatibility. This package does not
   manufacture those equations.
6. Arbitrary source weak limits are not asserted to satisfy every final DLR
   compatibility required by a wrapper; the comparison theorem itself needs
   no such bridge.
7. The critical comparison $1-p_c(G^*)\ge p_c(G)$ needed to merge the primal
   and dual parameter windows is not proved here.
8. Main statements are at interior $0<p<1$ with $q\ne1$. The $q=1$
   supercritical endpoint and other endpoint extensions are not supplied.

## Verification

Sixteen fully-qualified principal audits appear in `Audit.lean`. Fresh Lean
4.35 compilation at default heartbeats reports only `propext`,
`Classical.choice`, and `Quot.sound`. Run `./check.sh` from
`results/fk-qcritical`.
