# Finite-product FKG / Harris / Holley machinery, and the random-cluster lattice condition

**Public scope.** The generic finite-product FKG/Harris/Holley statements are complete in their class. The `clusterCount` application currently identifies only a $\mathbb F_2$-span corank, not the general connected-component count of the actual project graph, and `fkWeight` here is not identified with the repository's normalized labelled-multigraph `G.fkPMF`. These two identifications are real work, not definitional equalities inferred by a name. No Strassen coupling, inverse-limit comparison, or strict critical shift is supplied. The negative mirror remark prevents an invalid inference from log-submodularity to negative association; it is not a claim about all possible FK-specific anti-association results.


Member `m8`, swarm `smwu0pw30`, direction `d8`. Everything here is new to the
campaign: `rg -i "fkg|harris|holley|ahlswede"` over `results/fk-qcritical`
returns only incidental prose ("or FKG assumption is used"), so this is the
first formal FKG-type tool in the project.

The work is self-contained Lean, compiled against **the campaign repository's
own toolchain and Mathlib build** (Lean `v4.35.0`, Mathlib rev
`56a005855ea17e0b0958f73ec801ae140b0a1679`). No repository file is modified:
`build.sh` only *reads* `results/fk-qcritical/.lake`.

## Files and dependency order

| file | content |
|---|---|
| `FKG/Basic.lean` | two-point Chebyshev identity, `Fin.cons` reindexing and lattice algebra, the statements `LC` and `FKGstmt`, lattice condition on slices, monotone likelihood ratio (`mlr_LC`), Holley comparison at level `n` (`comparison`) |
| `FKG/Main.lean` | the induction: `fkg_succ` (lattice condition ⇒ FKG for one more coordinate) and the base case, giving `fkg_fin : ∀ n, FKGstmt n` |
| `FKG/General.lean` | transport to an arbitrary finite index type (`fkg_of_lattice`), product-Bernoulli lattice condition (`bernoulli_lc`), Harris (`harris`), Holley (`holley`) |
| `FKG/FKCluster.lean` | `𝔽₂`-edge vectors, graphic rank `edgeRank` and corank `clusterCount`, rank submodularity, cluster-count supermodularity, `fkWeight`, a two-vertex check |
| `FKG/Mirror.lean` | the antitone (decreasing-observable) form `fkg_antitone`, plus the documented **false** mirror statement |
| `FKG/FKApply.lean` | exact FK pair identity, lattice condition for `q ≥ 1`, reversed lattice condition for `q ≤ 1`, monotone likelihood ratio and Holley comparison in the edge activity, positive association (observable and event forms) |
| `FKG/Audit.lean` | `#print axioms` for the 18 main declarations |

## Main statements

All in namespace `FinFKG`, all with `V E : Type`, `[Fintype V] [DecidableEq V]`,
`[Fintype E] [DecidableEq E]` where relevant, and `ι` an arbitrary finite index
type for the general forms.

**1. The FKG theorem on a finite Boolean product.**  For
`P : (ι → Bool) → ℝ` strictly positive and log-supermodular,

```
hlc : ∀ x y, P x * P y ≤ P (x ⊔ y) * P (x ⊓ y)
```

increasing nonnegative `f g` satisfy

```
fkg_of_lattice : (∑ x, P x * f x) * (∑ x, P x * g x)
                   ≤ (∑ x, P x) * (∑ x, P x * f x * g x)
```

i.e. in normalized form `E[fg] ≥ E[f]E[g]`.  (`fkg_fin : ∀ n, FKGstmt n` is the
`Fin n` version from which it is transported.)

**2. Harris.** `harris`: for a product Bernoulli weight
`bernWeight p x = ∏ i, (if x i then p i else 1 - p i)` with `0 < p i < 1`, the
same inequality holds; the per-coordinate factor satisfies the lattice
condition **with equality** (`bernoulli_factor`, `bernoulli_lc`).

**3. Holley.** `holley`: if `P > 0` is log-supermodular and the likelihood
ratio `Q/P` is increasing (`hmlr : ∀ x y, P x * Q y ≤ Q (x ⊔ y) * P (x ⊓ y)`),
then `(∑ P f)(∑ Q) ≤ (∑ P)(∑ Q f)` for increasing nonnegative `f` — increasing
observables are larger under `Q`.

**4. Antitone form.** `fkg_antitone`: the same inequality for decreasing
nonnegative observables.  This is not an extra assumption: for a finite space
every observable is bounded, and the substitution `F = M - f`, `G = M - g`
turns the increasing statement into the decreasing one *and back* (the
`M`-dependent terms cancel because both sides carry the same total mass).  So
the decreasing form is equivalent to the increasing form; it is recorded
because closed events are decreasing.

**5. Cluster-count supermodularity.** For `ends : E → V × V`, with edge vectors
`χ_e = 1_{u} + 1_{w}` over `ZMod 2` and `clusterCount ends S = |V| -
finrank(span{χ_e : e ∈ S})`,

```
clusterCount_supermodular : clusterCount S + clusterCount T
                              ≤ clusterCount (S ∪ T) + clusterCount (S ∩ T)
```

from submodularity of the graphic rank (`edgeRank_submodular`, which is
`Submodule.finrank_sup_add_finrank_inf_eq` plus monotonicity of `finrank`).
Also `clusterCount_empty : clusterCount ∅ = |V|`, `clusterCount_antitone`, and
the check `clusterCount_two_vertex`: on the two-vertex graph with one edge the
value is `2` with no open edge and `1` with the edge open.

**6. The random-cluster weight and its lattice condition.** With
`fkWeight c q ends ω = c ^ |openSet ω| * q ^ clusterCount (openSet ω)`:

* `fkWeight_pair_eq`: there is `Δ : ℕ` with
  `k(x∨y) + k(x∧y) = k x + k y + Δ` and
  `w (x ⊔ y) * w (x ⊓ y) = w x * w y * q ^ Δ` — the exact defect identity.
* `fkWeight_lc`  (`q ≥ 1`): the lattice condition `w x * w y ≤ w (x⊔y) * w (x⊓y)`.
* `fk_association`, `fk_association_events` (`q ≥ 1`): positive association of
  the FK weight for increasing observables, and for increasing events.
* `fkWeight_lc_rev` (`0 < q ≤ 1`): the **reversed** lattice condition
  `w (x⊔y) * w (x⊓y) ≤ w x * w y`.  Nothing else is claimed for `q ≤ 1`.
* `fkWeight_mlr`, `fk_mono_activity`: for `0 < c₁ ≤ c₂` and `q ≥ 1` the
  likelihood ratio is increasing, hence by Holley
  `(∑ w_{c₁} f)(∑ w_{c₂}) ≤ (∑ w_{c₁})(∑ w_{c₂} f)` for increasing `f`:
  monotonicity of the random-cluster weight in the edge activity.  In the usual
  parametrization `c = p/(1-p)` this is monotonicity in `p`; the statement is
  in unnormalized form and normalizes by dividing by the two masses.

## A negative result: `q ≤ 1` does **not** give negative association

The mirror statement "a log-submodular weight makes increasing observables
negatively correlated" is **false**, and is not claimed anywhere in this
development.  Counterexample (documented in `FKG/Mirror.lean`): on one
coordinate the lattice condition is vacuous (both sides are literally the same
product), while for a weight with `P(0) = a > 0`, `P(1) = b > 0` and the
increasing observable `f = g = 𝟙{1}`,

```
(∑ P f g) * (∑ P) = (a+b)·b    >    b·b = (∑ P f) * (∑ P g).
```

This is exactly the `q < 1` regime of the random-cluster weight, so for `q ≤ 1`
only the reversed lattice condition is available.  (Equivalently: FKG is not a
symmetric statement — log-supermodularity implies positive association, but
log-submodularity does not imply negative association.)

## Proof architecture of the FKG theorem

Induction on the index type.  Step (`fkg_succ`), splitting the last coordinate
into the two slices `P₀ = P(·,0)`, `P₁ = P(·,1)` of masses `λ₀`, `λ₁`:

1. each slice satisfies the lattice condition (`LC.slice`);
2. applying the lattice condition to `(1,y)` and `(0,x)` gives the monotone
   likelihood ratio `P₀ x · P₁ y ≤ P₁ (x ⊔ y) · P₀ (x ⊓ y)` (`mlr_LC`), i.e.
   `P₁/P₀` is increasing;
3. the induction hypothesis per slice plus that monotone ratio give
   `E_{P₀}[f] ≤ E_{P₁}[f]` for increasing `f` (`comparison`, Holley's step,
   where the FKG inequality for `P₀` is applied to the likelihood ratio);
4. the two-point Chebyshev identity
   `(λ₀α₀+λ₁α₁)(λ₀β₀+λ₁β₁) ≤ (λ₀+λ₁)(λ₀α₀β₀+λ₁α₁β₁)` — a rewrite of
   `λ₀λ₁(α₀-α₁)(β₀-β₁) ≥ 0` (`chebyshev_two`) — closes the step.

No Hall/marriage theorem, no linear-programming duality, no Strassen coupling,
no rational approximation, no compactness, and default heartbeats throughout.

## Build and audit

```bash
cd <this directory>
./build.sh FKG/Basic.lean FKG/Main.lean FKG/General.lean \
           FKG/FKCluster.lean FKG/Mirror.lean FKG/FKApply.lean FKG/Audit.lean
```

`build.sh` puts this directory first on `LEAN_PATH` and appends the campaign
repository's `lake` build directories (Mathlib and its dependencies), and uses
`~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`.  Exact figures from a
clean rebuild (all `.olean` deleted first, 4 cores):

```
FKG/Basic.lean      2.30 s
FKG/Main.lean       2.64 s
FKG/General.lean    2.59 s
FKG/FKCluster.lean  2.39 s
FKG/Mirror.lean     2.88 s
FKG/FKApply.lean    2.51 s
FKG/Audit.lean      2.46 s
total wall          17.8 s
```

(An earlier clean rebuild of the six non-audit files measured 17.2 s with the
same command; run-to-run variation is under 10%.)  Per-file time is dominated by importing
Mathlib.

Audit (`FKG/Audit.lean`) prints, for all 18 audited declarations, exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorry`, `admit`, custom axiom, `unsafe`, or `native_decide` in the
sources.

## Scope and residuals (explicit)

Proved here: the finite-product FKG/Harris/Holley theorems; cluster-count
supermodularity for the graphic corank; the exact FK defect identity, the
lattice condition for `q ≥ 1`, the reversed condition for `q ≤ 1`, and
monotonicity in the edge activity with the exact hypotheses.

**Not** proved here, and not claimed:

1. The identity `clusterCount S = (number of connected components of the open
   subgraph)` is the standard graphic-matroid rank formula and is **not**
   formalized; only the corank *definition*, its supermodularity, and the
   two-vertex/two-value check are.  Consequence: `fkWeight` is proved to be a
   log-supermodular weight in the class "`q^{corank}`", but its identification
   with the labelled-multigraph FK PMF of `results/fk-qcritical/FK/FiniteModel.lean`
   is not formalized either.
2. Nothing infinite-volume: no cylinder limits, no DLR/Gibbs identity, no
   one-edge conditionals, no coupling existence (Strassen's hard direction),
   no planar duality, no enhanced/AG window.  In particular the existence of a
   monotone *coupling* is not derived here; only the expectation inequalities.
3. No strictness conclusion.  `fk_mono_activity` is a non-strict comparison;
   upgrading it to a strict increment requires an essential-enhancement input
   and is not attempted.

## Where this plugs into the campaign

* `fk_association` supplies the positive association of finite random-cluster
  measures at `q ≥ 1` that is otherwise missing from the development (the
  proof-status file repeatedly notes that a result "does not use FKG", which
  this makes available rather than avoided).
* `fk_mono_activity` supplies monotonicity of the random-cluster weight in
  `p` at fixed `q ≥ 1` (previously only Bernoulli monotonicity and "monotone
  analytic profiles" for the AG devices existed).
* `harris` gives finite-volume positive association for the independent
  (Bernoulli/activation) product laws used by the AG reference laws.
* `holley` is the reuse point for any future boundary-condition comparison:
  everything reduces to checking a monotone likelihood ratio.
* The negative remark prevents the plausible but false step "`q < 1` ⇒
  negative association", which the reversed lattice condition invites.
