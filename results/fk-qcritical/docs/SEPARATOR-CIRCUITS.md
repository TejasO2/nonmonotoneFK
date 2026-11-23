# Two-sided separators replace round spheres in the plane-dual circuit chain

Public module: `FK/SeparatorCircuits.lean`, verified independently before integration.  It imports only
public modules of `results/fk-qcritical`:

```
FK.EmbeddedCircuitSeparation, FK.PrimalOpenBoundary, FK.InfiniteOpenCircuitUniqueness,
Mathlib.Analysis.Convex.Gauge, Mathlib.Topology.Order.IntermediateValue
```

No shared or release file is modified, no `sorry`/`admit`/`axiom`/`unsafe`, no
heartbeat override, pinned toolchain `leanprover/lean4:v4.35.0`.

Check (exactly, from the repository root):

```bash
cd results/fk-qcritical
PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH \
  lake env lean ../../.ultramath/smwttt0li/m5/SeparatorCircuits.lean
```

It exits `0` with no diagnostics (no errors and no linter warnings).
`SeparatorCircuitsAudit.lean` is the same file plus 35 `#print axioms`
commands; `SeparatorCircuits.audit.txt` is the captured output.  Every audited
declaration reports exactly `propext`, `Classical.choice`, `Quot.sound`; there is
no `sorryAx`.

## The restriction that this module removes

The published chain in `FK.InfiniteOpenCircuitUniqueness` and
`FK.PrimalOpenBoundary` fixes the *shape and the centre* of every barrier:

* `SphericalOpenCircuit R ω C c r` requires `0 < r`, `vertex v ∉ sphere c r` for
  all `v`, and `crossing : R.CrossingControlledBy (sphere c r) C`.
* `HasOpenCircuitExhaustion R ω c` requires such a circuit at every radius
  `ρ < r` **about the same centre `c`**.
* `SphericalPrimalCircuitGeometry` / `SphericalDualCircuitGeometry` attach one
  metric sphere `sphere (centre C) (radius C)` to each dual circuit `C`, and
  `hasOpenCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries`
  (`FK/PrimalOpenBoundary.lean:394`) additionally forces `c = S.centre C`.

A plane embedding does not supply concentric spheres: the boundary of a face of a
rectangular grid is a square, the boundary of a dual open component is a generic
Jordan curve, and — critically — the *centre* `c` of the exhaustion is the
reference point of the ambient space, not something a dual circuit can choose.
`FK/PrimalOpenBoundary.lean` already proves the finite cut/circuit step and the
uniqueness assembly; the shape restriction is what stands between those and a
general geometric input.

## What is constructed

### 1. The separation datum, and its exact characterisation

```lean
structure TwoSidedSeparation (X : Type*) [TopologicalSpace X] where
  K : Set X                        -- the barrier
  inside : Set X
  outside : Set X
  cover : Kᶜ ⊆ inside ∪ outside
  separated : ∀ ⦃x y⦄, x ∈ inside → y ∈ outside → ¬ JoinedIn Kᶜ x y
```

The datum is not an extra assumption hidden in the interface; it is *exactly*
"the inside is a union of path components of the complement of the barrier":

* `twoSidedSeparationOfPathComponents (K) (inside) (hcomp)` builds a
  `TwoSidedSeparation` from any `inside` closed under `pathComponentIn Kᶜ`;
* `pathComponentIn_subset_inside_of_mem` proves the converse for every
  `TwoSidedSeparation`:
  `x ∈ S.inside → pathComponentIn S.Kᶜ x ⊆ S.inside`.

So the interface states precisely the Jordan-type content, and it is discharged
(not assumed) in the instances below.

### 2. Level sets separate (the abstract form of the circle argument)

```lean
theorem not_joinedIn_compl_levelSet_of_lt {f : X → ℝ} (hf : Continuous f) {a : ℝ}
    {x y : X} (hx : f x < a) (hy : a < f y) : ¬ JoinedIn (f ⁻¹' {a})ᶜ x y
```

This is the intermediate-value theorem, and it subsumes the existing
`FK.CircleSeparation.not_joinedIn_compl_sphere_of_inside_outside`, which is
re-derived as `not_joinedIn_compl_sphere_of_inside_outside_separator` with
`f = fun z => dist z c`, `a = r`.  No Jordan curve theorem is used; the module
does not assume one.

### 3. Every convex body is a barrier (genuinely non-round geometry)

```lean
theorem not_joinedIn_compl_convexFrontier_of_interior_notMem_closure {s : Set E}
    (hconv : Convex ℝ s) (hnhds : s ∈ 𝓝 (0 : E)) {x y : E}
    (hx : x ∈ interior s) (hy : y ∉ closure s) : ¬ JoinedIn (frontier s)ᶜ x y
```

Proof: the Minkowski functional `gauge s` is continuous
(`continuous_gauge`), is `< 1` exactly on `interior s`
(`gauge_lt_one_iff_mem_interior`), is `≤ 1` exactly on `closure s`
(`gauge_le_one_iff_mem_closure`) and equals `1` exactly on `frontier s`
(`gauge_eq_one_iff_mem_frontier`); the level-set theorem above finishes.  The
resulting `convexSeparation hconv hnhds : TwoSidedSeparation E` has
`K = frontier s`, `inside = interior s`, `outside = (closure s)ᶜ`, using
`compl_frontier_eq_interior_union_compl_closure`.

A square, a triangle, a polygon, a convex polygon obtained from a face boundary:
all of them are admissible barriers, with no circle and no centre anywhere.

Two further proved facts make the `crossing` field of the circuit interface cheap
to discharge for a straight-line drawing:

```lean
theorem convex_segment_subset_interior {s : Set E} (hconv : Convex ℝ s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ interior s) : segment ℝ x y ⊆ interior s
theorem segment_notMem_convexFrontier ... : p ∈ segment ℝ x y → p ∉ frontier s
```

So an edge with both endpoints inside the body never meets the barrier; only the
edges that really cross the frontier have to be listed in the circuit label set.

### 4. The whole open-circuit chain, unchanged

For a `SimpleGraph` realized in a real normed space:

* `SeparatorOpenCircuit R ω C S` (fields `vertex_off`, `crossing`, `label_open`,
  `openConnected`) replaces `SphericalOpenCircuit`;
* `mem_inside_or_exists_vertexOnLabels_of_walk` and
  `exists_vertexOnLabels_of_openConnected_inside_outside` are the walk-induction
  and escaping-walk lemmas, proved from `cover`/`separated` instead of
  `compl_sphere_eq_ball_union_outside`;
* `openConnected_of_two_infinite_of_separatorOpenCircuit` joins two infinite open
  components meeting the inside, given only that finitely many vertices lie
  inside;
* `HasSeparatorCircuitExhaustion R ω c` demands, for each `ρ`, a circuit whose
  `inside` contains `ball c ρ` and carries finitely many vertices;
* `globalAtMostOne_of_separatorCircuitExhaustion` is the `GlobalAtMostOne`
  assembly.  Note that the *global* properness hypothesis
  `∀ r, (vertex ⁻¹' ball c r).Finite` of the spherical theorem is not needed: the
  finiteness comes with each circuit.

The closed-label trapping lemmas `mem_inside_of_walk_of_closed` and
`mem_inside_of_openConnected_of_closed` (an open walk whose crossing labels are
closed never leaves the inside) are the separator forms of the published
`mem_ball_of_openConnected_sphere`.

Conservativity is proved, not asserted:
`separatorOpenCircuit_of_sphericalOpenCircuit`,
`hasSeparatorCircuitExhaustion_of_hasOpenCircuitExhaustion`, and the recovered
published conclusion `globalAtMostOne_of_openCircuitExhaustion_via_separator`.

### 5. Cofinality from one fixed convex shape (no common centre)

```lean
theorem exists_smul_ball_subset_interior {s : Set E} (hnhds : s ∈ 𝓝 (0 : E)) (ρ : ℝ) :
    ∃ t : ℝ, 0 < t ∧ ball (0 : E) ρ ⊆ interior (t • s)
```

so scaling alone makes the insides cofinal.  Consequently

```lean
theorem hasSeparatorCircuitExhaustion_of_scaled_convexBody
    (R) (ω) {s : Set E} (hconv : Convex ℝ s) (hnhds : s ∈ 𝓝 (0 : E))
    (hcirc : ∀ (t : ℝ) (ht : 0 < t), ∃ C, SeparatorOpenCircuit R ω C
        (convexSeparation (hconv.smul t) (smul_mem_nhds_zero_of_mem_nhds hnhds ht)))
    (hfinite : ∀ (t : ℝ) (ht : 0 < t), (vertex ⁻¹' (convexSeparation (hconv.smul t)
        (smul_mem_nhds_zero_of_mem_nhds hnhds ht)).inside).Finite) :
    HasSeparatorCircuitExhaustion R ω 0

theorem globalAtMostOne_of_scaled_convexBody ... : GlobalAtMostOne G ω
```

The geometric work is now: find *one* convex body and, at each scale, one circuit
whose arcs are the only arcs meeting its frontier.  The centre no longer has to
be the same for every circuit, and the shape no longer has to be a ball.

### 6. The interface is strictly wider than the spherical one, in two senses

**(a) An interface-level witness.**  The half-space

```lean
def halfSpaceSeparation : TwoSidedSeparation ℂ          -- K = {z | z.re = 1}
theorem halfSpaceSeparation_not_sphere (c : ℂ) (r : ℝ) :
    sphere c r ≠ halfSpaceSeparation.K
```

is a separator (level set of `Complex.re` at `1`) that is not a sphere, because
spheres are bounded (`Metric.isBounded_sphere`,
`Metric.isBounded_iff_subset_closedBall`) and the vertical line at real part `1`
is not.  A half-space cannot be scaled into a cofinal family, however.

**(b) A witness inside the cofinally usable class.**  The frontier of the closed
unit square is *not* any metric sphere:

```lean
def closedSquare : Set ℂ                                  -- |re| ≤ 1, |im| ≤ 1
theorem closedSquare_frontier_not_sphere (c : ℂ) (r : ℝ) :
    sphere c r ≠ frontier closedSquare
```

Proof.  Write `c = c₁ + c₂ i`.  The points `1 + i`, `1 - i`, `-1 + i` and `1` are
in the frontier: each is in the closed square, and each has a coordinate equal
to `1`, so it is not interior (`re_eq_one_notMem_interior`,
`im_eq_one_notMem_interior`: moving outward by `ε/2` stays in every ball of
radius `ε` and leaves the square; `mem_frontier_iff_notMem_interior`).  If the
frontier were `sphere c r`, all four would satisfy
`(z - c).re ^ 2 + (z - c).im ^ 2 = r ^ 2` (`Complex.sq_norm`,
`Complex.normSq_apply`).  Comparing `1 + i` with `-1 + i` gives `c₁ = 0`;
comparing `1 + i` with `1` then gives `c₂ = 1/2` and `r ^ 2 = 5/4`; but `1 - i`
then gives `r ^ 2 = 13/4`.  `nlinarith` closes the contradiction.

Because `closedSquare` is convex and a neighbourhood of the origin, its
*scalings* are exactly the cofinal family used by
`hasSeparatorCircuitExhaustion_of_scaled_convexBody`.  So the convex-body
exhaustion is genuinely beyond the concentric-sphere exhaustion, which is the
rectangular obstruction that motivated the generalization.

### 7. Labelled port: dual circuits, cuts, and finiteness

```lean
structure SeparatorDualCircuitGeometry (P : LabelledDualPair) (R) where
  sep : Set P.Edge → TwoSidedSeparation E
  vertex_off : ∀ C, P.faceDual.cycleMatroid.IsCircuit C → ∀ v, vertex v ∈ (sep C).Kᶜ
  crossing   : ∀ C, ..., R.CrossingControlledBy (sep C).K C
  finite_inside : ∀ C, ..., (vertex ⁻¹' (sep C).inside).Finite

theorem openVertexComponent_finite_of_separator
    (R) (S : TwoSidedSeparation E) (hcross) (hclosed : ∀ e ∈ C, ω e = false)
    (hfinite) (hx : vertex x ∈ S.inside) :
    (P.primal.openVertexComponent ω x).Finite

theorem exists_dualOpen_circuit_boundary_openComponent_finite_of_separator
    (R) (S : SeparatorDualCircuitGeometry P R) (hP : P.GraphicDualCertificate) (ω) (x)
    (he : e ∈ P.primal.vertexCut (P.primal.openVertexComponent ω x)) :
    ∃ C, C ⊆ P.primal.vertexCut (...) ∧ e ∈ C ∧
      P.faceDual.cycleMatroid.IsCircuit C ∧
      C ⊆ P.faceDual.openEdgeSet (dualConfig (Equiv.refl P.Edge) ω) ∧
      (vertex x ∈ (S.sep C).inside → (P.primal.openVertexComponent ω x).Finite)
```

and on the primal-circuit side (`SeparatorPrimalCircuitGeometry`):

```lean
theorem separatorOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary ...
theorem hasSeparatorCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries
    (S) (ω) (c)
    (hcofinal : ∀ ρ, ∃ x C, C ⊆ P.faceDual.vertexCut (component of x) ∧
      P.primal.cycleMatroid.IsCircuit C ∧ ball c ρ ⊆ (S.sep C).inside) :
    HasSeparatorCircuitExhaustion R (P.primal.simpleConfig hloop ω) c
theorem globalAtMostOne_of_cofinal_dualOpenComponentBoundaries_separator ...
```

The last two are the separator replacements for
`FK.PrimalOpenBoundary.hasOpenCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries`
and `...globalAtMostOne_of_cofinal_dualOpenComponentBoundaries`, with the
condition `c = S.centre C` replaced by the honest inclusion
`ball c ρ ⊆ (S.sep C).inside`.

`separatorDualCircuitGeometry_of_sphericalDualCircuitGeometry` records that the
labelled spherical geometry is an instance, once vertex properness of the spheres
is supplied (the third field genuinely needs it; the spherical structure does not
carry it).

## Exact residuals

Nothing here constructs a continuous embedding of an arbitrary planar graph, and
nothing here derives the circuits from dual nonpercolation.  The precise
geometric obligations that remain are:

1. **Realization.**  A `LabelledPathRealization` (or `OpenPathRealization`) of the
   graph by continuous arcs, plus, for each circuit `C` used, a convex body `s_C`
   with `vertex_off` (no vertex on `frontier s_C`) and `crossing` (every arc
   meeting `frontier s_C` is a `C`-arc).  The theorems above show this is all that
   is needed for the finite-component and uniqueness conclusions; they do not
   construct such an `s_C`.
2. **Vertex properness inside the barrier** for each used circuit
   (`finite_inside`).
3. **Cofinality of the circuit family**, in the weak form
   `ball c ρ ⊆ (sep C).inside`; obtained automatically by scaling when a single
   convex body works at every scale, but not constructed here.
4. **Dual nonpercolation ⇒ cofinal dual-open components** is untouched; that is a
   separate step (and is the subject of another member's direction).

## Non-claims

* No proof that a face boundary of a rectangular grid is Jordan, and no
  construction of a graph whose *only* barriers are non-spherical.  What is
  formalised is: the interface strictly contains the spherical one, both at the
  interface level (half-space) and inside the scalably-cofinal convex class
  (the unit square), and convexity is the only hypothesis needed on the body for
  the separation theorem.
* No Theorem 1.11, no full strong uniqueness, no critical-window statement, no
  `GlobalAtMostOne` for any infinite concrete graph beyond what the published
  spherical theorems already gave.
* The published files are not edited; the coordinator decides integration.
