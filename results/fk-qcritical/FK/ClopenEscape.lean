import FK.OneEdgeNoEscape

/-!
# Clopen escape families and no mass escape for FK weak limits

`FK/OneEdgeNoEscape.lean` reduces the infinite-volume one-point conditional
identity of an FK weak limit to a *no mass escape* statement.  That file
records the equivalence with the scalar mass identity and several
reformulations, but it never proves the estimate from a geometric hypothesis.

This file supplies the missing *spatial* input in the exact form in which
at-most-one-cluster produces it: a family of **clopen escape events**

`esc m`  =  "the connection is only achieved outside the fixed finite box `m`",

which is decreasing in `m`, carried by the limit law with vanishing mass, and a
superset of the part of the stage-`k` connection event that the fixed box `m`
does not already explain.  The estimates themselves (`farVanishing` and
`noEscape`) never use monotonicity of the stage events `C k` in `k`; only the
final assembly into a one-point identity does, because it routes through
`OneEdgeNoEscape.onePoint_edge_of_noEscape`, which derives the rate hypotheses
from `C k ↑ C∞`.  A non-monotone schedule therefore needs, in addition, a
moving-clopen-set integral argument (see `RESULTS.md`, section 1.2).

Contents:

* `tendsto_measure_of_isClopen`, `tendsto_measure_escape`: clopen set masses
  converge along weak convergence, and the mass of a decreasing family of
  clopen escape events converges to the mass of its intersection.
* `farVanishing_of_clopen_escape`: the small-box far-vanishing estimate
  `μ_k (C k \ lower m) ≤ ε` eventually, for a fixed `m`.
* `noEscape_of_clopen_escape`: the limsup no-mass-escape inequality
  `limsup_k μ_k (C k) ≤ μ C∞` for a monotone stage family.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

local instance (priority := 10000) classicalDecEqInstanceClopenEscape (α : Type*) :
    DecidableEq α := Classical.decEq α

attribute [local instance] Classical.decEq

namespace FK.InfiniteVolume

local instance boundaryPartitionMeasurableSpaceClopenEscape (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

namespace ClopenEscape

variable {E : Type*} [Countable E]

/-! ## Part 1: clopen masses and their decreasing limits -/

/-- Weak convergence gives convergence of the masses of every clopen set. -/
theorem tendsto_measure_of_isClopen {A : Set (Configuration E)} (hA : IsClopen A)
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun k => ((μs k : Measure (Configuration E)) A)) atTop
      (𝓝 (((μ : Measure (Configuration E)) A))) := by
  have hfr : (μ : Measure (Configuration E)) (frontier A) = 0 := by
    rw [isClopen_iff_frontier_eq_empty.mp hA]; simp
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hfr

/-- Real-valued form of `tendsto_measure_of_isClopen`. -/
theorem tendsto_measure_toReal_of_isClopen {A : Set (Configuration E)} (hA : IsClopen A)
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun k => ((μs k : Measure (Configuration E)) A).toReal) atTop
      (𝓝 (((μ : Measure (Configuration E)) A).toReal)) :=
  ENNReal.tendsto_toReal (by simp) |>.comp (tendsto_measure_of_isClopen hA hμ)

/-- **Continuity from above for a decreasing family of clopen escape events.** -/
theorem tendsto_measure_escape (μ : Measure (Configuration E)) [IsFiniteMeasure μ]
    {esc : ℕ → Set (Configuration E)} (hesc : ∀ m, IsClopen (esc m))
    (hanti : Antitone esc) :
    Tendsto (fun m => μ (esc m)) atTop (𝓝 (μ (⋂ m, esc m))) := by
  refine MeasureTheory.tendsto_measure_iInter_atTop (fun m => ?_) hanti ⟨0, measure_ne_top μ _⟩
  exact ((hesc m).isClosed.measurableSet).nullMeasurableSet

/-- Real-valued form of `tendsto_measure_escape`, with a null intersection. -/
theorem tendsto_measure_toReal_escape (μ : Measure (Configuration E)) [IsFiniteMeasure μ]
    {esc : ℕ → Set (Configuration E)} (hesc : ∀ m, IsClopen (esc m))
    (hanti : Antitone esc) (hnull : μ (⋂ m, esc m) = 0) :
    Tendsto (fun m => (μ (esc m)).toReal) atTop (𝓝 0) := by
  have h1 := tendsto_measure_escape μ hesc hanti
  rw [hnull] at h1
  have h2 : Tendsto (fun m => (μ (esc m)).toReal) atTop (𝓝 ((0 : ℝ≥0∞)).toReal) :=
    ENNReal.tendsto_toReal (by simp) |>.comp h1
  simpa using h2

/-! ## Part 2: far vanishing of the unexplained stage mass -/

/-- **Fixed-box far vanishing from a clopen escape family.**

Suppose `lower m` are clopen approximations of the limiting connection event,
increasing in `m`, each contained in every sufficiently late stage connection
event `C k`, and suppose whatever the stage event achieves beyond `lower m` is
absorbed by a clopen escape event `esc m`.  If the escape events decrease and
carry no mass in the limit, then the mass of `C k \ lower m` is eventually
arbitrarily small for a suitable fixed `m`.  This is precisely the
`farVanishing` hypothesis of `scalar_of_farVanishing`, but proved rather than
assumed. -/
theorem farVanishing_of_clopen_escape
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ))
    {C : ℕ → Set (Configuration E)} {lower esc : ℕ → Set (Configuration E)}
    (_hlowerCl : ∀ m, IsClopen (lower m))
    (hescCl : ∀ m, IsClopen (esc m))
    (_hsub : ∀ m k, m ≤ k → lower m ⊆ C k)
    (hsdiff : ∀ m k, m ≤ k → C k \ lower m ⊆ esc m)
    (hescAnti : Antitone esc)
    (hescNull : (μ : Measure (Configuration E)) (⋂ m, esc m) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ᶠ k in atTop,
      ((μs k : Measure (Configuration E)) (C k \ lower m)).toReal ≤ ε := by
  intro ε hε
  have hsmall : Tendsto (fun m => ((μ : Measure (Configuration E)) (esc m)).toReal) atTop (𝓝 0) :=
    tendsto_measure_toReal_escape (μ : Measure (Configuration E)) hescCl hescAnti hescNull
  obtain ⟨m, hm⟩ : ∃ m, ((μ : Measure (Configuration E)) (esc m)).toReal < ε := by
    have hex : ∀ᶠ m in atTop, ((μ : Measure (Configuration E)) (esc m)).toReal < ε :=
      hsmall.eventually (isOpen_Iio.mem_nhds hε)
    exact hex.exists
  refine ⟨m, ?_⟩
  have hcl : Tendsto (fun k => ((μs k : Measure (Configuration E)) (esc m)).toReal) atTop
      (𝓝 (((μ : Measure (Configuration E)) (esc m)).toReal)) :=
    tendsto_measure_toReal_of_isClopen (hescCl m) hμ
  filter_upwards [eventually_ge_atTop m,
    hcl.eventually (isOpen_Iio.mem_nhds hm)] with k hk hkm
  exact (ENNReal.toReal_mono (by simp) (measure_mono (hsdiff m k hk))).trans hkm.le

/-! ## Part 3: the limsup no-mass-escape inequality -/

/-- **No mass escape from a monotone stage family and a clopen escape family.**

If the stage connection events `C k` increase to `C∞`, and everything that a
stage event achieves beyond the fixed `C m` is absorbed by a clopen escape event
`esc m` whose masses vanish in the limit, then no mass escapes:
`limsup_k μ_k (C k) ≤ μ C∞`.  This is the hypothesis `hnoEscape` of
`onePoint_edge_of_noEscape`. -/
theorem noEscape_of_clopen_escape
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ))
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)} {esc : ℕ → Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hUnion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hescCl : ∀ m, IsClopen (esc m))
    (hsdiff : ∀ m k, m ≤ k → C k \ C m ⊆ esc m)
    (hescAnti : Antitone esc)
    (hescNull : (μ : Measure (Configuration E)) (⋂ m, esc m) = 0) :
    Filter.limsup (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
      ≤ ((μ : Measure (Configuration E)) Cinf).toReal := by
  classical
  set s : ℕ → ℝ := fun k => ((μs k : Measure (Configuration E)) (C k)).toReal with hs
  -- the mass of `C k` is carried by the fixed `C m` plus the escape event
  have hsplit : ∀ m k, m ≤ k →
      ((μs k : Measure (Configuration E)) (C k)).toReal
        ≤ ((μs k : Measure (Configuration E)) (C m)).toReal
          + ((μs k : Measure (Configuration E)) (esc m)).toReal := by
    intro m k hmk
    have hsub : C m ⊆ C k := hCmono hmk
    have hmeas : MeasurableSet (C k \ C m) :=
      ((hCcl k).isOpen.measurableSet).diff ((hCcl m).isOpen.measurableSet)
    have hun : C m ∪ (C k \ C m) = C k := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hsub hx
        · exact hx.1
      · intro hx
        by_cases hxm : x ∈ C m
        · exact Or.inl hxm
        · exact Or.inr ⟨hx, hxm⟩
    have hsum : (μs k : Measure (Configuration E)) (C k)
        = (μs k : Measure (Configuration E)) (C m)
          + (μs k : Measure (Configuration E)) (C k \ C m) := by
      conv_lhs => rw [← hun]
      exact measure_union disjoint_sdiff_right hmeas
    have hle : (μs k : Measure (Configuration E)) (C k \ C m)
        ≤ (μs k : Measure (Configuration E)) (esc m) := measure_mono (hsdiff m k hmk)
    rw [hsum, ENNReal.toReal_add (by simp) (by simp)]
    have := ENNReal.toReal_mono (by simp : (μs k : Measure (Configuration E)) (esc m) ≠ ⊤) hle
    linarith
  -- hence the limsup is at most the fixed box mass plus the escape mass
  have hstep : ∀ m, Filter.limsup s atTop
      ≤ ((μ : Measure (Configuration E)) (C m)).toReal
        + ((μ : Measure (Configuration E)) (esc m)).toReal := by
    intro m
    have hev : ∀ᶠ k in atTop, s k ≤ ((μs k : Measure (Configuration E)) (C m)).toReal
        + ((μs k : Measure (Configuration E)) (esc m)).toReal := by
      filter_upwards [eventually_ge_atTop m] with k hk
      exact hsplit m k hk
    have hlim : Tendsto (fun k => ((μs k : Measure (Configuration E)) (C m)).toReal
        + ((μs k : Measure (Configuration E)) (esc m)).toReal) atTop
        (𝓝 (((μ : Measure (Configuration E)) (C m)).toReal
          + ((μ : Measure (Configuration E)) (esc m)).toReal)) :=
      (tendsto_measure_toReal_of_isClopen (hCcl m) hμ).add
        (tendsto_measure_toReal_of_isClopen (hescCl m) hμ)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hfin : ∀ᶠ k in atTop, ((μs k : Measure (Configuration E)) (C m)).toReal
        + ((μs k : Measure (Configuration E)) (esc m)).toReal
        ≤ (((μ : Measure (Configuration E)) (C m)).toReal
          + ((μ : Measure (Configuration E)) (esc m)).toReal) + ε := by
      have hlt : (((μ : Measure (Configuration E)) (C m)).toReal
          + ((μ : Measure (Configuration E)) (esc m)).toReal)
            < (((μ : Measure (Configuration E)) (C m)).toReal
          + ((μ : Measure (Configuration E)) (esc m)).toReal) + ε := by linarith
      exact hlim.eventually (eventually_le_nhds hlt)
    have hmem : ∀ᶠ k in atTop, s k ≤ (((μ : Measure (Configuration E)) (C m)).toReal
        + ((μ : Measure (Configuration E)) (esc m)).toReal) + ε :=
      hfin.and hev |>.mono fun k hk => hk.2.trans hk.1
    have hcob : IsCoboundedUnder (· ≤ ·) atTop s := by
      refine ⟨0, fun a ha => ?_⟩
      have ha' : ∀ᶠ k in atTop, s k ≤ a := Filter.eventually_map.mp ha
      obtain ⟨k, hk⟩ := ha'.exists
      exact le_trans ENNReal.toReal_nonneg hk
    exact Filter.limsup_le_of_le hcob hmem
  -- let the fixed box grow and the escape mass vanish
  have hun : Cinf = ⋃ m, C m := by
    ext x
    rw [Set.mem_iUnion]
    exact (hUnion x).symm
  have hbox : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop
      (𝓝 (((μ : Measure (Configuration E)) Cinf).toReal)) := by
    have h1 : Tendsto (fun m => (μ : Measure (Configuration E)) (C m)) atTop
        (𝓝 ((μ : Measure (Configuration E)) (⋃ m, C m))) :=
      MeasureTheory.tendsto_measure_iUnion_atTop (μ := (μ : Measure (Configuration E)))
        (s := C) hCmono
    have h2 : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop
        (𝓝 (((μ : Measure (Configuration E)) (⋃ m, C m))).toReal) :=
      ENNReal.tendsto_toReal (by simp) |>.comp h1
    simpa [hun] using h2
  have hesc : Tendsto (fun m => ((μ : Measure (Configuration E)) (esc m)).toReal) atTop (𝓝 0) :=
    tendsto_measure_toReal_escape (μ : Measure (Configuration E)) hescCl hescAnti hescNull
  have htot : Tendsto (fun m => (((μ : Measure (Configuration E)) (C m)).toReal
      + ((μ : Measure (Configuration E)) (esc m)).toReal)) atTop
      (𝓝 (((μ : Measure (Configuration E)) Cinf).toReal + 0)) := hbox.add hesc
  have hfin : Tendsto (fun m => (((μ : Measure (Configuration E)) (C m)).toReal
      + ((μ : Measure (Configuration E)) (esc m)).toReal)) atTop
      (𝓝 (((μ : Measure (Configuration E)) Cinf).toReal)) := by
    simpa using htot
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hfin
    (Eventually.of_forall fun m => hstep m)

/-! ## Part 4: box DLR from a clopen escape family -/

/-- **The full weak-limit DLR theorem for a stabilising specification.**

Fix a box `B` and a measurable target boundary assignment `αspec`.  Suppose

* the finite-stage laws `μs k` satisfy, for every edge of `B`, the exact
  one-point FK conditional identity with the two-valued rate which is `α` on the
  stage connection event `C e k` and `β` off it (this is the finite specification
  step `hfin`, whose proof needs the nesting of the exhaustion);
* the stage connection events `C e k` are clopen and increase to `Cinf e`;
* the parts of `C e k` that the fixed finite box `m` does not explain are
  absorbed by clopen escape events `esc e m` which decrease to a set of
  `μ`-measure zero (this is exactly what at-most-one-cluster supplies);
* the limit rate `OneEdgeNoEscape.twoValuedRate α β (Cinf e)` is the box specification's open
  rate for `αspec`.

Then `μ` is a DLR (Gibbs) law at the box `B` for the specification `αspec`.
Every remaining input is a displayed hypothesis: no monotonicity or pointwise
convergence of the stage *rates* is assumed, only the clopen escape estimates. -/
theorem isDLR_of_clopen_escape
    (B : FiniteBox E) {q p : NNReal}
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (αspec : B.Exterior → B.BoundaryPartition) (hαspec : Measurable αspec)
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : (e : B.edges) → ℕ → Set (Configuration E)}
    {Cinf : (e : B.edges) → Set (Configuration E)}
    {esc : (e : B.edges) → ℕ → Set (Configuration E)}
    (hCcl : ∀ (e : B.edges) k, IsClopen (C e k))
    (hCmono : ∀ (e : B.edges), Monotone (C e))
    (hUnion : ∀ (e : B.edges) ω, (∃ k, ω ∈ C e k) ↔ ω ∈ Cinf e)
    (hescCl : ∀ (e : B.edges) m, IsClopen (esc e m))
    (hsdiff : ∀ (e : B.edges) m k, m ≤ k → C e k \ C e m ⊆ esc e m)
    (hescAnti : ∀ (e : B.edges), Antitone (esc e))
    (hescNull : ∀ (e : B.edges), (μ : Measure (Configuration E)) (⋂ m, esc e m) = 0)
    (hfin : ∀ (e : B.edges) (k : ℕ)
      (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (OneEdgeNoEscape.twoValuedRate α β (C e k) ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (hrate : ∀ (e : B.edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      OneEdgeNoEscape.twoValuedRate α β (Cinf e) ω
        = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
            (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    B.IsDLR hq hp₁.le αspec hαspec μ := by
  classical
  refine B.isDLR_of_hasOnePointConditionals hq hp₀ hp₁ αspec hαspec μ ?_
  refine (B.hasOnePointConditionals_iff_bif αspec μ).mpr ?_
  intro e g hg
  have hnoEsc := noEscape_of_clopen_escape (E := E) hμ (hCcl e) (hCmono e) (hUnion e)
    (hescCl e) (hsdiff e) (hescAnti e) (hescNull e)
  exact OneEdgeNoEscape.onePoint_edge_of_noEscape B e μs μ hα0 hαβ hβ1
    (hCcl e) (hCmono e) (hUnion e) (hfin e) hμ hnoEsc αspec (hrate e) g hg

/-! ## Part 5: escape mass bounded by a dominating law

The clopen route above transfers escape masses from `μ` to the stage laws `μs k`
by weak convergence.  A second, often cheaper route replaces weak convergence by
*stochastic domination* by a fixed law `ν`: if the escape events are increasing
and `ν` carries them with vanishing mass, then the same far-vanishing estimate
holds with no compactness or clopenness input at all.  This is the form used in
the subcritical regime, where `ν` is a subcritical Bernoulli measure whose
connection tails decay exponentially. -/

/-- **Far vanishing from a dominating law.** -/
theorem farVanishing_of_dominated_escape
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {C : ℕ → Set (Configuration E)} {lower esc : ℕ → Set (Configuration E)}
    (hsdiff : ∀ m k, m ≤ k → C k \ lower m ⊆ esc m)
    (hescMeas : ∀ m, MeasurableSet (esc m)) (hescUp : ∀ m, IsUpperSet (esc m))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ k, FKLimit.StochasticallyDominates ν (μs k))
    (hν : Tendsto (fun m => ((ν : Measure (Configuration E)) (esc m)).toReal) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ᶠ k in atTop,
      ((μs k : Measure (Configuration E)) (C k \ lower m)).toReal ≤ ε := by
  intro ε hε
  obtain ⟨m, hm⟩ : ∃ m, ((ν : Measure (Configuration E)) (esc m)).toReal < ε :=
    (hν.eventually (isOpen_Iio.mem_nhds hε)).exists
  refine ⟨m, ?_⟩
  filter_upwards [eventually_ge_atTop m] with k hk
  have h1 : (μs k : Measure (Configuration E)) (C k \ lower m)
      ≤ (μs k : Measure (Configuration E)) (esc m) := measure_mono (hsdiff m k hk)
  have h2 : (μs k : Measure (Configuration E)) (esc m)
      ≤ (ν : Measure (Configuration E)) (esc m) :=
    FKLimit.ennreal_le_of_probabilityMeasure_apply_le (hdom k (esc m) (hescMeas m) (hescUp m))
  exact (ENNReal.toReal_mono (by simp) (h1.trans h2)).trans hm.le

/-- **No mass escape from a dominating law.** -/
theorem noEscape_of_dominated_escape
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ))
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)} {esc : ℕ → Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hUnion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hsdiff : ∀ m k, m ≤ k → C k \ C m ⊆ esc m)
    (hescMeas : ∀ m, MeasurableSet (esc m)) (hescUp : ∀ m, IsUpperSet (esc m))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ k, FKLimit.StochasticallyDominates ν (μs k))
    (hν : Tendsto (fun m => ((ν : Measure (Configuration E)) (esc m)).toReal) atTop (𝓝 0)) :
    Filter.limsup (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
      ≤ ((μ : Measure (Configuration E)) Cinf).toReal := by
  classical
  set s : ℕ → ℝ := fun k => ((μs k : Measure (Configuration E)) (C k)).toReal with hs
  have hstep : ∀ m, Filter.limsup s atTop
      ≤ ((μ : Measure (Configuration E)) (C m)).toReal
        + ((ν : Measure (Configuration E)) (esc m)).toReal := by
    intro m
    have hev : ∀ᶠ k in atTop, ((μs k : Measure (Configuration E)) (C k)).toReal
        ≤ ((μs k : Measure (Configuration E)) (C m)).toReal
          + ((ν : Measure (Configuration E)) (esc m)).toReal := by
      filter_upwards [eventually_ge_atTop m] with k hk
      have hsub : C m ⊆ C k := hCmono hk
      have hmeas : MeasurableSet (C k \ C m) :=
        ((hCcl k).isOpen.measurableSet).diff ((hCcl m).isOpen.measurableSet)
      have hun : C m ∪ (C k \ C m) = C k := by
        ext x
        constructor
        · rintro (hx | hx)
          · exact hsub hx
          · exact hx.1
        · intro hx
          by_cases hxm : x ∈ C m
          · exact Or.inl hxm
          · exact Or.inr ⟨hx, hxm⟩
      have hsum : (μs k : Measure (Configuration E)) (C k)
          = (μs k : Measure (Configuration E)) (C m)
            + (μs k : Measure (Configuration E)) (C k \ C m) := by
        conv_lhs => rw [← hun]
        exact measure_union disjoint_sdiff_right hmeas
      have hle1 : (μs k : Measure (Configuration E)) (C k \ C m)
          ≤ (μs k : Measure (Configuration E)) (esc m) := measure_mono (hsdiff m k hk)
      have hle2 : (μs k : Measure (Configuration E)) (esc m)
          ≤ (ν : Measure (Configuration E)) (esc m) :=
        FKLimit.ennreal_le_of_probabilityMeasure_apply_le
          (hdom k (esc m) (hescMeas m) (hescUp m))
      have hle := hle1.trans hle2
      rw [hsum, ENNReal.toReal_add (by simp) (by simp)]
      have h2 := ENNReal.toReal_mono (by simp : (ν : Measure (Configuration E)) (esc m) ≠ ⊤) hle
      linarith
    have hlim : Tendsto (fun k => ((μs k : Measure (Configuration E)) (C m)).toReal
        + ((ν : Measure (Configuration E)) (esc m)).toReal) atTop
        (𝓝 (((μ : Measure (Configuration E)) (C m)).toReal
          + ((ν : Measure (Configuration E)) (esc m)).toReal)) :=
      (tendsto_measure_toReal_of_isClopen (hCcl m) hμ).add tendsto_const_nhds
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hfin : ∀ᶠ k in atTop, ((μs k : Measure (Configuration E)) (C m)).toReal
        + ((ν : Measure (Configuration E)) (esc m)).toReal
        ≤ (((μ : Measure (Configuration E)) (C m)).toReal
          + ((ν : Measure (Configuration E)) (esc m)).toReal) + ε := by
      have hlt : (((μ : Measure (Configuration E)) (C m)).toReal
          + ((ν : Measure (Configuration E)) (esc m)).toReal)
            < (((μ : Measure (Configuration E)) (C m)).toReal
          + ((ν : Measure (Configuration E)) (esc m)).toReal) + ε := by linarith
      exact hlim.eventually (eventually_le_nhds hlt)
    have hmem : ∀ᶠ k in atTop, s k ≤ (((μ : Measure (Configuration E)) (C m)).toReal
        + ((ν : Measure (Configuration E)) (esc m)).toReal) + ε :=
      hfin.and hev |>.mono fun k hk => hk.2.trans hk.1
    have hcob : IsCoboundedUnder (· ≤ ·) atTop s := by
      refine ⟨0, fun a ha => ?_⟩
      have ha' : ∀ᶠ k in atTop, s k ≤ a := Filter.eventually_map.mp ha
      obtain ⟨k, hk⟩ := ha'.exists
      exact le_trans ENNReal.toReal_nonneg hk
    exact Filter.limsup_le_of_le hcob hmem
  have hun : Cinf = ⋃ m, C m := by
    ext x
    rw [Set.mem_iUnion]
    exact (hUnion x).symm
  have hbox : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop
      (𝓝 (((μ : Measure (Configuration E)) Cinf).toReal)) := by
    have h1 : Tendsto (fun m => (μ : Measure (Configuration E)) (C m)) atTop
        (𝓝 ((μ : Measure (Configuration E)) (⋃ m, C m))) :=
      MeasureTheory.tendsto_measure_iUnion_atTop (μ := (μ : Measure (Configuration E)))
        (s := C) hCmono
    have h2 : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop
        (𝓝 (((μ : Measure (Configuration E)) (⋃ m, C m))).toReal) :=
      ENNReal.tendsto_toReal (by simp) |>.comp h1
    simpa [hun] using h2
  have htot : Tendsto (fun m => (((μ : Measure (Configuration E)) (C m)).toReal
      + ((ν : Measure (Configuration E)) (esc m)).toReal)) atTop
      (𝓝 (((μ : Measure (Configuration E)) Cinf).toReal)) := by
    have := hbox.add hν
    simpa using this
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htot
    (Eventually.of_forall fun m => hstep m)

/-- **The full weak-limit DLR theorem in the dominant-tail form.**

Same conclusion as `isDLR_of_clopen_escape`, but the escape masses are
controlled by a fixed dominating law `ν` instead of by weak convergence, so no
clopenness of the escape sets is needed.  The three inputs are the finite-stage
one-point identities (`hfin`, the finite specification/nesting step), the
combinatorial escape inclusion (`hsdiff`, supplied by
`ClusterEscape.escape_pair_of_wiredConn`), and the vanishing escaping-cluster
tails of the dominating law (`hν`, supplied in the subcritical regime by a
Bernoulli arm bound). -/
theorem isDLR_of_dominated_escape
    (B : FiniteBox E) {q p : NNReal}
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (αspec : B.Exterior → B.BoundaryPartition) (hαspec : Measurable αspec)
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : (e : B.edges) → ℕ → Set (Configuration E)}
    {Cinf : (e : B.edges) → Set (Configuration E)}
    {esc : (e : B.edges) → ℕ → Set (Configuration E)}
    (hCcl : ∀ (e : B.edges) k, IsClopen (C e k))
    (hCmono : ∀ (e : B.edges), Monotone (C e))
    (hUnion : ∀ (e : B.edges) ω, (∃ k, ω ∈ C e k) ↔ ω ∈ Cinf e)
    (hsdiff : ∀ (e : B.edges) m k, m ≤ k → C e k \ C e m ⊆ esc e m)
    (hescMeas : ∀ (e : B.edges) m, MeasurableSet (esc e m))
    (hescUp : ∀ (e : B.edges) m, IsUpperSet (esc e m))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ k, FKLimit.StochasticallyDominates ν (μs k))
    (hν : ∀ (e : B.edges),
      Tendsto (fun m => ((ν : Measure (Configuration E)) (esc e m)).toReal) atTop (𝓝 0))
    (hfin : ∀ (e : B.edges) (k : ℕ)
      (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (OneEdgeNoEscape.twoValuedRate α β (C e k) ω)
            * g (B.splitOff e ω) ∂(μs k : Measure (Configuration E)))
    (hrate : ∀ (e : B.edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      OneEdgeNoEscape.twoValuedRate α β (Cinf e) ω
        = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
            (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    B.IsDLR hq hp₁.le αspec hαspec μ := by
  classical
  refine B.isDLR_of_hasOnePointConditionals hq hp₀ hp₁ αspec hαspec μ ?_
  refine (B.hasOnePointConditionals_iff_bif αspec μ).mpr ?_
  intro e g hg
  have hnoEsc := noEscape_of_dominated_escape (E := E) hμ (hCcl e) (hCmono e) (hUnion e)
    (hsdiff e) (hescMeas e) (hescUp e) ν hdom (hν e)
  exact OneEdgeNoEscape.onePoint_edge_of_noEscape B e μs μ hα0 hαβ hβ1
    (hCcl e) (hCmono e) (hUnion e) (hfin e) hμ hnoEsc αspec (hrate e) g hg

/-- Measurable form of `tendsto_measure_toReal_escape`: vanishing of the
intersection is enough, clopenness of the escape sets is not needed.  This is
the form in which a *dominating* law's escaping-cluster tails vanish, e.g. under
nonpercolation. -/
theorem tendsto_measure_toReal_escape_of_measurable (μ : Measure (Configuration E))
    [IsFiniteMeasure μ] {esc : ℕ → Set (Configuration E)}
    (hesc : ∀ m, MeasurableSet (esc m)) (hanti : Antitone esc)
    (hnull : μ (⋂ m, esc m) = 0) :
    Tendsto (fun m => (μ (esc m)).toReal) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m => μ (esc m)) atTop (𝓝 (μ (⋂ m, esc m))) :=
    MeasureTheory.tendsto_measure_iInter_atTop (fun m => (hesc m).nullMeasurableSet)
      hanti ⟨0, measure_ne_top μ _⟩
  rw [hnull] at h1
  have h2 : Tendsto (fun m => (μ (esc m)).toReal) atTop (𝓝 ((0 : ℝ≥0∞)).toReal) :=
    ENNReal.tendsto_toReal (by simp) |>.comp h1
  simpa using h2

/-- **The weak-limit DLR theorem with a nonpercolating dominating law.**

`isDLR_of_dominated_escape` with the escape tails discharged from the
nonpercolation of the dominating law: if the escape events decrease to a
`ν`-null set (for instance because `ν`-a.s. the cluster of `x` never leaves all
of them, i.e. `ν` does not percolate), then the tails vanish and `μ` is a DLR
law at the box. -/
theorem isDLR_of_dominated_escape_of_null_escape
    (B : FiniteBox E) {q p : NNReal}
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (αspec : B.Exterior → B.BoundaryPartition) (hαspec : Measurable αspec)
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : (e : B.edges) → ℕ → Set (Configuration E)}
    {Cinf : (e : B.edges) → Set (Configuration E)}
    {esc : (e : B.edges) → ℕ → Set (Configuration E)}
    (hCcl : ∀ (e : B.edges) k, IsClopen (C e k))
    (hCmono : ∀ (e : B.edges), Monotone (C e))
    (hUnion : ∀ (e : B.edges) ω, (∃ k, ω ∈ C e k) ↔ ω ∈ Cinf e)
    (hsdiff : ∀ (e : B.edges) m k, m ≤ k → C e k \ C e m ⊆ esc e m)
    (hescMeas : ∀ (e : B.edges) m, MeasurableSet (esc e m))
    (hescUp : ∀ (e : B.edges) m, IsUpperSet (esc e m))
    (hescAnti : ∀ (e : B.edges), Antitone (esc e))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ k, FKLimit.StochasticallyDominates ν (μs k))
    (hnull : ∀ (e : B.edges), (ν : Measure (Configuration E)) (⋂ m, esc e m) = 0)
    (hfin : ∀ (e : B.edges) (k : ℕ)
      (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (OneEdgeNoEscape.twoValuedRate α β (C e k) ω)
            * g (B.splitOff e ω) ∂(μs k : Measure (Configuration E)))
    (hrate : ∀ (e : B.edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      OneEdgeNoEscape.twoValuedRate α β (Cinf e) ω
        = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
            (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    B.IsDLR hq hp₁.le αspec hαspec μ :=
  isDLR_of_dominated_escape B μ hμ αspec hαspec hα0 hαβ hβ1 hCcl hCmono hUnion hsdiff
    hescMeas hescUp ν hdom
    (fun e => tendsto_measure_toReal_escape_of_measurable (ν : Measure (Configuration E))
      (hescMeas e) (hescAnti e) (hnull e))
    hfin hrate hq hp₀ hp₁

/-- **Weak-limit DLR membership on a whole exhaustion (clopen route).**

This is the box-by-box assembly of `isDLR_of_clopen_escape` into the public
`FK.InfiniteVolume.DLRMeasures` class: the stage laws converge to `μ`, and for
*every* box of the exhaustion the stage connection events admit a clopen escape
family with vanishing limit mass.  Conclusion: `μ` is a DLR law for the
measurable boundary assignment `Φ` at every box, i.e. `μ ∈ DLRMeasures exh Φ`.
No monotonicity of the stage rates and no local constancy of `Φ` is used. -/
theorem mem_dlrMeasures_of_clopen_escape
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hp₀ : 0 < p) (hp₁ : p < 1) (hq : 0 < q)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto μs atTop (𝓝 μ))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    (C esc : (n : ℕ) → (e : (exh.box n).edges) → ℕ → Set (Configuration E))
    (Cinf : (n : ℕ) → (e : (exh.box n).edges) → Set (Configuration E))
    (hCcl : ∀ (n : ℕ) (e : (exh.box n).edges) k, IsClopen (C n e k))
    (hCmono : ∀ (n : ℕ) (e : (exh.box n).edges), Monotone (C n e))
    (hUnion : ∀ (n : ℕ) (e : (exh.box n).edges) ω, (∃ k, ω ∈ C n e k) ↔ ω ∈ Cinf n e)
    (hescCl : ∀ (n : ℕ) (e : (exh.box n).edges) m, IsClopen (esc n e m))
    (hsdiff : ∀ (n : ℕ) (e : (exh.box n).edges) m k, m ≤ k → C n e k \ C n e m ⊆ esc n e m)
    (hescAnti : ∀ (n : ℕ) (e : (exh.box n).edges), Antitone (esc n e))
    (hescNull : ∀ (n : ℕ) (e : (exh.box n).edges),
      (μ : Measure (Configuration E)) (⋂ m, esc n e m) = 0)
    (hfin : ∀ (n : ℕ) (e : (exh.box n).edges) (k : ℕ)
      (g : (exh.box n).Exterior × Glauber.OffConfig Bool (exh.box n).edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif (exh.box n).splitBit e ω then g ((exh.box n).splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (OneEdgeNoEscape.twoValuedRate α β (C n e k) ω)
            * g ((exh.box n).splitOff e ω) ∂(μs k : Measure (Configuration E)))
    (hrate : ∀ (n : ℕ) (e : (exh.box n).edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      OneEdgeNoEscape.twoValuedRate α β (Cinf n e) ω
        = Glauber.FKBridge.openRate (exh.box n).graph (q := q) (p := p)
            ((Φ.partition n) (((exh.box n).splitOff e ω).1)) e
            (((exh.box n).splitOff e ω).2)) :
    μ ∈ DLRMeasures exh Φ hq hp₁.le := by
  intro n
  exact isDLR_of_clopen_escape (B := exh.box n) (C := C n) (Cinf := Cinf n) (esc := esc n)
    (μs := μs) μ hμ (Φ.partition n) (Φ.measurable_partition n)
    hα0 hαβ hβ1 (hCcl n) (hCmono n) (hUnion n) (hescCl n)
    (hsdiff n) (hescAnti n) (hescNull n) (hfin n) (hrate n) hq hp₀ hp₁

end ClopenEscape

end FK.InfiniteVolume
