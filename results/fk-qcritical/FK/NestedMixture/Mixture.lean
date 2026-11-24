import FK.SpecificationNesting
import FK.GibbsOrder

/-!
# The nested-box FK mixture identity

For a finite labelled multigraph `G`, a vertex region `dom`, a set `I` of edge
labels with both endpoints in `dom`, q > 0 and 0 < p < 1:

* `fkPMF_combine_eq_fibreWeight_mul` — the joint FK mass of the glued
  configuration `combine I ζ ξ` factorises as the *fibre mass*
  `fibreWeight ξ = φ_G{ω | ω|Iᶜ = ξ}` times the sub-box FK mass of `ζ` under the
  exterior-induced partition `π(α,ξ)`.  This is the conditional law
  `φ^{π(α,ξ)}_Λ` in the source's §1.3 convention, obtained from the pointwise
  ratio of `FK.SpecificationNesting` plus normalisation of the sub-box law.
* `sum_fibreWeight` — the fibre masses sum to one, so the exterior marginal is
  a genuine probability distribution.
* `fkMeasure_cyl_eq_mixture` — the larger-box FK law of the cylinder over any
  interior event `A` equals the mixture `∑_ξ fibreWeight ξ · φ^{π(α,ξ)}_Λ(A)`.
  This is the genuine exterior-induced-partition mixture.
* `fkMeasure_cyl_ge_free` / `fkMeasure_cyl_le_wired` — at `q ≥ 1` every fibre is
  sandwiched between the free and wired sub-box laws (`FK.GibbsOrder`), so the
  cylinder mass of every increasing interior event is at least the sub-box free
  mass and at most the sub-box wired mass.

Everything here is unconditional finite-graph mathematics: no boundary
convention, no planarity, no DLR packaging, no growth hypothesis.
-/

open scoped Classical BigOperators ENNReal NNReal
open FK.Finite

namespace FK.NestedMixture

open FK.Finite.SpecificationNesting FK.Finite.LabelledMultigraph

variable {G : FK.Finite.LabelledMultigraph}

/-! ## Splitting a configuration into interior and exterior parts -/

/-- The pair `(interior, exterior)` of a configuration is a genuine
reindexing of the configuration space. -/
noncomputable def combineEquiv (I : Set G.Edge) :
    ((↥I → Bool) × ({e : G.Edge // e ∉ I} → Bool)) ≃ G.Configuration where
  toFun z := combine I z.1 z.2
  invFun ω := (restrictI I ω, fun e => ω (e : G.Edge))
  left_inv z := by
    refine Prod.ext ?_ ?_
    · funext e
      exact combine_of_mem I z.1 z.2 e
    · funext e
      exact combine_of_not_mem I z.1 z.2 e
  right_inv ω := by
    funext e
    by_cases h : e ∈ I
    · have := combine_of_mem I (restrictI I ω) (fun e => ω (e : G.Edge)) ⟨e, h⟩
      simpa [restrictI] using this
    · have := combine_of_not_mem I (restrictI I ω) (fun e => ω (e : G.Edge)) ⟨e, h⟩
      simpa using this

@[simp] lemma combineEquiv_apply (I : Set G.Edge)
    (z : (↥I → Bool) × ({e : G.Edge // e ∉ I} → Bool)) :
    combineEquiv I z = combine I z.1 z.2 := rfl

/-- The FK point masses sum to one. -/
theorem sum_fkPMF (G : FK.Finite.LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (π : G.BoundaryPartition) :
    ∑ ω : G.Configuration, G.fkPMF hq hp π ω = 1 := by
  rw [← PMF.tsum_coe (p := G.fkPMF hq hp π), tsum_fintype]

section Mixture

variable {dom : Set G.Vertex} {I : Set G.Edge}
variable {hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧ G.target (e : G.Edge) ∈ dom}
variable {q p : NNReal} {α : G.BoundaryPartition}

/-! ## Reindexing along the interior/exterior splitting -/

/-- Reindexing a configuration sum along the interior/exterior splitting. -/
theorem sum_combine {M : Type*} [AddCommMonoid M] (f : G.Configuration → M) :
    ∑ z : (↥I → Bool) × ({e : G.Edge // e ∉ I} → Bool), f (combine I z.1 z.2)
      = ∑ ω : G.Configuration, f ω := by
  rw [← Equiv.sum_comp (combineEquiv I) f]
  exact Finset.sum_congr rfl (fun z _ => by rw [combineEquiv_apply])

/-! ## The exterior-induced partition -/

/-- The exterior-induced boundary partition of the sub-box `Λ` (the source's
`π(α,η)`): reachability in the fixed graph.  It depends only on the exterior
configuration. -/
noncomputable def exteriorPartition (dom : Set G.Vertex) (I : Set G.Edge)
    (α : G.BoundaryPartition) (ξ : {e : G.Edge // e ∉ I} → Bool) : Setoid ↥dom :=
  inducedPartition dom I α (combine I (fun _ => false) ξ)

theorem inducedPartition_eq_exteriorPartition (ζ : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) :
    inducedPartition dom I α (combine I ζ ξ) = exteriorPartition dom I α ξ :=
  inducedPartition_congr (interiorClosed_combine I ζ (fun _ => false) ξ)

/-! ## Normalisation of the sub-box law -/

/-- The sub-box FK point masses sum to one (for any `Fintype` instance on the
interior configuration type; all choices agree). -/
theorem sum_subBox_fkPMF (i : Fintype (↥I → Bool)) (hq : 0 < q) (hp : p ≤ 1)
    (π : (subBox dom I hdom).BoundaryPartition) :
    @Finset.sum (↥I → Bool) ℝ≥0∞ _ (@Finset.univ _ i)
      (fun ζ => (subBox dom I hdom).fkPMF hq hp π ζ) = 1 := by
  letI := i
  rw [← PMF.tsum_coe (p := (subBox dom I hdom).fkPMF hq hp π)]
  rw [tsum_fintype]

/-! ## Fibre weights -/

/-- The mass of the exterior fibre: the probability that the sub-box edges have
the configuration `ξ` (equivalently the sum of the joint masses over all
interior configurations on top of `ξ`). -/
noncomputable def fibreWeight (hq : 0 < q) (hp : p ≤ 1) (α : G.BoundaryPartition)
    (ξ : {e : G.Edge // e ∉ I} → Bool) : ℝ≥0∞ :=
  ∑ ζ : ↥I → Bool, (G.fkPMF hq hp α) (combine I ζ ξ)

theorem sum_fibreWeight (hq : 0 < q) (hp : p ≤ 1) :
    ∑ ξ : ({e : G.Edge // e ∉ I} → Bool), fibreWeight (I := I) hq hp α ξ = 1 := by
  classical
  have h1 : (∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
      ∑ ζ : ↥I → Bool, (G.fkPMF hq hp α) (combine I ζ ξ))
      = ∑ z : (↥I → Bool) × ({e : G.Edge // e ∉ I} → Bool),
          (G.fkPMF hq hp α) (combine I z.1 z.2) := by
    rw [Finset.sum_comm]
    exact (Fintype.sum_prod_type (f := fun z : (↥I → Bool) ×
      ({e : G.Edge // e ∉ I} → Bool) => (G.fkPMF hq hp α) (combine I z.1 z.2))).symm
  have h2 : (∑ ξ : ({e : G.Edge // e ∉ I} → Bool), fibreWeight (I := I) hq hp α ξ)
      = ∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          ∑ ζ : ↥I → Bool, (G.fkPMF hq hp α) (combine I ζ ξ) := rfl
  rw [h2, h1, sum_combine (I := I) (fun ω => (G.fkPMF hq hp α) ω)]
  exact sum_fkPMF G hq hp α

/-- **Conditional factorialisation of the joint FK mass.**  The joint mass of a
glued configuration is the exterior fibre mass times the sub-box FK mass under
the exterior-induced partition. -/
theorem fkPMF_combine_eq_fibreWeight_mul (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (ζ : ↥I → Bool) (ξ : {e : G.Edge // e ∉ I} → Bool) :
    (G.fkPMF hq hp1.le α) (combine I ζ ξ)
      = fibreWeight (I := I) hq hp1.le α ξ *
          ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ := by
  classical
  have hratio : ∀ ζ' : ↥I → Bool,
      (G.fkPMF hq hp1.le α) (combine I ζ ξ) *
          ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ'
        = (G.fkPMF hq hp1.le α) (combine I ζ' ξ) *
          ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ := by
    intro ζ'
    have h := fkPMF_conditional_ratio (dom := dom) (I := I) (hdom := hdom) hq hp0 hp1
      α ζ ζ' ξ
    rwa [inducedPartition_eq_exteriorPartition (dom := dom) (I := I) (α := α) ζ ξ] at h
  have hb : ∑ ζ' : ↥I → Bool,
      ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ' = 1 :=
    sum_subBox_fkPMF (dom := dom) (I := I) (hdom := hdom) _ hq hp1.le _
  calc (G.fkPMF hq hp1.le α) (combine I ζ ξ)
      = (G.fkPMF hq hp1.le α) (combine I ζ ξ) *
          ∑ ζ' : ↥I → Bool,
            ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ' := by
        rw [hb, mul_one]
    _ = ∑ ζ' : ↥I → Bool,
          (G.fkPMF hq hp1.le α) (combine I ζ ξ) *
            ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ' := by
        rw [Finset.mul_sum]
    _ = ∑ ζ' : ↥I → Bool,
          (G.fkPMF hq hp1.le α) (combine I ζ' ξ) *
            ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ := by
        exact Finset.sum_congr rfl (fun ζ' _ => hratio ζ')
    _ = (∑ ζ' : ↥I → Bool, (G.fkPMF hq hp1.le α) (combine I ζ' ξ)) *
          ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ := by
        rw [Finset.sum_mul]
    _ = fibreWeight (I := I) hq hp1.le α ξ *
          ((subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ)) ζ := rfl

/-! ## The mixture identity -/

/-- The mass of an interior event under the sub-box law, as a sum of point
masses. -/
theorem subBox_fkMeasure_apply (hq : 0 < q) (hp : p ≤ 1)
    (π : (subBox dom I hdom).BoundaryPartition) (A : Set (↥I → Bool)) :
    (subBox dom I hdom).fkMeasure hq hp π A
      = ∑ ζ : ↥I → Bool, if ζ ∈ A then (subBox dom I hdom).fkPMF hq hp π ζ else 0 := by
  rw [fkMeasure, PMF.toMeasure_apply_fintype]
  rfl

/-- **The exterior-induced-partition mixture identity.**  The larger-box FK mass
of the cylinder over an interior event `A` is the mixture of the sub-box laws
with the exterior-induced partitions, weighted by the realised exterior. -/
theorem fkMeasure_cyl_eq_mixture (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (A : Set (↥I → Bool)) :
    G.fkMeasure hq hp1.le α {ω : G.Configuration | restrictI I ω ∈ A}
      = ∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          fibreWeight (I := I) hq hp1.le α ξ *
            (subBox dom I hdom).fkMeasure hq hp1.le (exteriorPartition dom I α ξ) A := by
  classical
  have hLHS : G.fkMeasure hq hp1.le α {ω : G.Configuration | restrictI I ω ∈ A}
      = ∑ ω : G.Configuration,
          if restrictI I ω ∈ A then (G.fkPMF hq hp1.le α) ω else 0 := by
    rw [fkMeasure, PMF.toMeasure_apply_fintype]
    rfl
  rw [hLHS]
  rw [← Equiv.sum_comp (combineEquiv I)
    (fun ω => if restrictI I ω ∈ A then (G.fkPMF hq hp1.le α) ω else 0)]
  rw [Fintype.sum_prod_type]
  have hstep : ∀ (ζ : ↥I → Bool) (ξ : {e : G.Edge // e ∉ I} → Bool),
      (if restrictI I (combine I ζ ξ) ∈ A then
          (G.fkPMF hq hp1.le α) (combine I ζ ξ) else 0)
        = fibreWeight (I := I) hq hp1.le α ξ *
            (if ζ ∈ A then
              (subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ) ζ
              else 0) := by
    intro ζ ξ
    rw [restrictI_combine, fkPMF_combine_eq_fibreWeight_mul (dom := dom) (I := I)
      (hdom := hdom) (G := G) hq hp0 hp1 ζ ξ]
    by_cases h : ζ ∈ A
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  calc (∑ ζ : ↥I → Bool,
        (if restrictI I (combine I ζ ξ) ∈ A then
          (G.fkPMF hq hp1.le α) (combine I ζ ξ) else 0))
      = ∑ ζ : ↥I → Bool, fibreWeight (I := I) hq hp1.le α ξ *
          (if ζ ∈ A then
            (subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ) ζ else 0) :=
        Finset.sum_congr rfl (fun ζ _ => hstep ζ ξ)
    _ = fibreWeight (I := I) hq hp1.le α ξ *
          ∑ ζ : ↥I → Bool, (if ζ ∈ A then
            (subBox dom I hdom).fkPMF hq hp1.le (exteriorPartition dom I α ξ) ζ else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ = fibreWeight (I := I) hq hp1.le α ξ *
          (subBox dom I hdom).fkMeasure hq hp1.le (exteriorPartition dom I α ξ) A := by
        rw [subBox_fkMeasure_apply]

/-! ## The free/wired sandwich of the mixture -/

/-- **The cylinder mass of an increasing interior event dominates the sub-box
free law** at `q ≥ 1`. -/
theorem fkMeasure_cyl_ge_free {q : NNReal} (hq1 : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    {A : Set (↥I → Bool)} (hA : IsUpperSet A) :
    (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
        (subBox dom I hdom).freeBoundary A
      ≤ G.fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le α
          {ω : G.Configuration | restrictI I ω ∈ A} := by
  classical
  rw [fkMeasure_cyl_eq_mixture (dom := dom) (I := I) (hdom := hdom)
    (lt_of_lt_of_le zero_lt_one hq1) hp0 hp1 A]
  have hle : ∀ ξ : ({e : G.Edge // e ∉ I} → Bool),
      (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
          (subBox dom I hdom).freeBoundary A
        ≤ (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
            (exteriorPartition dom I α ξ) A :=
    fun ξ => (subBox dom I hdom).fkMeasure_mono_wiring hq1 hp0 hp1
      ((subBox dom I hdom).freeBoundary_le _) hA
  calc (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
        (subBox dom I hdom).freeBoundary A
      = (∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          fibreWeight (I := I) (lt_of_lt_of_le zero_lt_one hq1) hp1.le α ξ) *
          (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
            (subBox dom I hdom).freeBoundary A := by
        rw [sum_fibreWeight (I := I) (G := G)
          (lt_of_lt_of_le zero_lt_one hq1) hp1.le]
        exact (one_mul _).symm
    _ = ∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          fibreWeight (I := I) (lt_of_lt_of_le zero_lt_one hq1) hp1.le α ξ *
            (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
              (subBox dom I hdom).freeBoundary A :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          fibreWeight (I := I) (lt_of_lt_of_le zero_lt_one hq1) hp1.le α ξ *
            (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
              (exteriorPartition dom I α ξ) A :=
        Finset.sum_le_sum (fun ξ _ =>
          mul_le_mul_of_nonneg_left (hle ξ) (by positivity))

/-- **The cylinder mass of an increasing interior event is dominated by the
sub-box wired law** at `q ≥ 1`. -/
theorem fkMeasure_cyl_le_wired {q : NNReal} (hq1 : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    {A : Set (↥I → Bool)} (hA : IsUpperSet A) :
    G.fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le α
        {ω : G.Configuration | restrictI I ω ∈ A}
      ≤ (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
          (subBox dom I hdom).wiredBoundary A := by
  classical
  rw [fkMeasure_cyl_eq_mixture (dom := dom) (I := I) (hdom := hdom)
    (lt_of_lt_of_le zero_lt_one hq1) hp0 hp1 A]
  have hle : ∀ ξ : ({e : G.Edge // e ∉ I} → Bool),
      (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
          (exteriorPartition dom I α ξ) A
        ≤ (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
            (subBox dom I hdom).wiredBoundary A :=
    fun ξ => (subBox dom I hdom).fkMeasure_mono_wiring hq1 hp0 hp1
      ((subBox dom I hdom).le_wiredBoundary _) hA
  calc (∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          fibreWeight (I := I) (lt_of_lt_of_le zero_lt_one hq1) hp1.le α ξ *
            (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
              (exteriorPartition dom I α ξ) A)
      ≤ ∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          fibreWeight (I := I) (lt_of_lt_of_le zero_lt_one hq1) hp1.le α ξ *
            (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
              (subBox dom I hdom).wiredBoundary A :=
        Finset.sum_le_sum (fun ξ _ =>
          mul_le_mul_of_nonneg_left (hle ξ) (by positivity))
    _ = (∑ ξ : ({e : G.Edge // e ∉ I} → Bool),
          fibreWeight (I := I) (lt_of_lt_of_le zero_lt_one hq1) hp1.le α ξ) *
          (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
            (subBox dom I hdom).wiredBoundary A :=
        (Finset.sum_mul _ _ _).symm
    _ = (subBox dom I hdom).fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le
          (subBox dom I hdom).wiredBoundary A := by
        rw [sum_fibreWeight (I := I) (G := G)
          (lt_of_lt_of_le zero_lt_one hq1) hp1.le, one_mul]

end Mixture

end FK.NestedMixture

/-! ## Axiom audit -/

#print axioms FK.NestedMixture.fkPMF_combine_eq_fibreWeight_mul
#print axioms FK.NestedMixture.sum_fibreWeight
#print axioms FK.NestedMixture.fkMeasure_cyl_eq_mixture
#print axioms FK.NestedMixture.fkMeasure_cyl_ge_free
#print axioms FK.NestedMixture.fkMeasure_cyl_le_wired
