import FK.NestedTransportGeneral
import FK.NestedMixture.NestedBox

/-! The global DLR form of the nested finite FK specification identity. -/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Classical BigOperators

namespace FK.NestedFinDLR

open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.SpecificationNesting
open FK.InfiniteVolume
open FK.NestedMixture

universe u v

variable {E : Type u} [Countable E]

section PMFFactorization

variable {G : LabelledMultigraph} {dom : Set G.Vertex} {I : Set G.Edge}
variable {hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧ G.target (e : G.Edge) ∈ dom}
variable {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (α : G.BoundaryPartition)

/-- The exterior fibre masses packaged as the probability mass function they are. -/
noncomputable def fibrePMF : PMF ({e : G.Edge // e ∉ I} → Bool) :=
  PMF.ofFintype (fibreWeight (I := I) hq hp₁.le α) (sum_fibreWeight hq hp₁.le)

@[simp] lemma fibrePMF_apply (ξ : {e : G.Edge // e ∉ I} → Bool) :
    fibrePMF hq hp₁ α ξ = fibreWeight (I := I) hq hp₁.le α ξ := by
  exact PMF.ofFintype_apply _ _

include hp₀

/-- The joint FK law is the exterior fibre followed by the induced sub-box FK law. -/
theorem map_fibrePMF_bind_subBox :
    PMF.map (fun z : (↥I → Bool) × ({e : G.Edge // e ∉ I} → Bool) =>
        combine I z.1 z.2)
      ((fibrePMF (I := I) hq hp₁ α).bind fun ξ =>
        PMF.map (fun ζ => (ζ, ξ))
          ((subBox dom I hdom).fkPMF hq hp₁.le (exteriorPartition dom I α ξ))) =
      G.fkPMF hq hp₁.le α := by
  apply PMF.ext
  intro ω
  rw [PMF.map_apply]
  let z := (combineEquiv (G := G) I).symm ω
  rw [tsum_eq_single z]
  · simp only [show ω = combine I z.1 z.2 by
      change ω = combineEquiv I z
      simp [z], if_true]
    rw [PMF.bind_apply]
    let ξ₀ : {e : G.Edge // e ∉ I} → Bool := fun e => ω e.1
    have hz : z = (restrictI I ω, ξ₀) := by
      apply (combineEquiv (G := G) I).injective
      simp [z, ξ₀, combineEquiv]
    rw [tsum_eq_single ξ₀]
    · rw [fibrePMF_apply, PMF.map_apply]
      rw [tsum_eq_single (restrictI I ω)]
      · rw [hz]
        simp only [Prod.mk.injEq, true_and, if_true]
        exact (fkPMF_combine_eq_fibreWeight_mul hq hp₀ hp₁ _ _).symm
      · intro ζ hζ
        have hne : z ≠ (ζ, ξ₀) := by
          rw [hz]
          intro h
          exact hζ (congrArg Prod.fst h).symm
        simp [hne]
    · intro ξ hξ
      have hzξ : z.2 ≠ ξ := by
        rw [hz]
        exact fun h => hξ h.symm
      have hne : ∀ ζ, z ≠ (ζ, ξ) := by
        intro ζ h
        exact hzξ (congrArg Prod.snd h)
      simp [PMF.map_apply, hne]
  · intro z' hz'
    have hne : ω ≠ combine I z'.1 z'.2 := by
      intro h
      apply hz'
      apply (combineEquiv (G := G) I).injective
      simpa [z] using h.symm
    simp [hne]


end PMFFactorization

section MeasurePMF

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem toMeasure_eq_sum_smul_dirac (ν : PMF X) :
    ν.toMeasure = Measure.sum (fun x => ν x • Measure.dirac x) := by
  apply Measure.ext
  intro s hs
  rw [Measure.sum_apply _ hs, ν.toMeasure_apply hs]
  apply tsum_congr
  intro x
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  by_cases hx : x ∈ s <;> simp [hx]

lemma lintegral_toMeasure (ν : PMF X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂ν.toMeasure) = ∑' x, ν x * f x := by
  rw [toMeasure_eq_sum_smul_dirac, lintegral_sum_measure]
  apply tsum_congr
  intro x
  rw [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

/-- Comp-product with a PMF-valued kernel is exactly its PMF bind. -/
theorem compProd_toMeasure_eq_toMeasure_bind
    (ν : PMF X) (κ : X → PMF Y)
    (κm : X → Measure Y) (hκ : ∀ x, κm x = (κ x).toMeasure)
    (hmeas : Measurable κm) (hprob : ∀ x, IsProbabilityMeasure (κm x)) :
    ν.toMeasure ⊗ₘ
      ({ toFun := κm, measurable' := hmeas } : ProbabilityTheory.Kernel X Y) =
      (ν.bind fun x => PMF.map (Prod.mk x) (κ x)).toMeasure := by
  let K : ProbabilityTheory.Kernel X Y := { toFun := κm, measurable' := hmeas }
  letI : ProbabilityTheory.IsMarkovKernel K := { isProbabilityMeasure := hprob }
  change ν.toMeasure ⊗ₘ K = _
  apply Measure.ext
  intro s hs
  rw [Measure.compProd_apply hs, PMF.toMeasure_bind_apply _ _ _ hs]
  rw [lintegral_toMeasure]
  · apply tsum_congr
    intro x
    change ν x * κm x (Prod.mk x ⁻¹' s) = _
    rw [hκ, PMF.toMeasure_map_apply _ _ _ measurable_prodMk_left hs]
  · exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := K) hs

end MeasurePMF


section NestedBoxDLR

open FK.NestedMixture.NestedBox

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

variable {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
variable {B C : FiniteBox E} (N : NestedBox B C)

/-- The part of a small-box exterior configuration lying in the larger box. -/
noncomputable def annulusOfExterior (η : B.Exterior) : {e : C.graph.Edge // e ∉ N.ide} → Bool :=
  fun e => η ⟨(e.1 : E), e.2⟩

/-- The exact exterior-induced boundary partition of the source's specification. -/
noncomputable def inducedBoundary (α : C.BoundaryPartition) (η : B.Exterior) :
    B.BoundaryPartition :=
  Setoid.comap N.vertEquiv.symm
    (exteriorPartition N.dom N.ide α (annulusOfExterior N η))

lemma measurable_annulusOfExterior : Measurable (annulusOfExterior N (B := B) (C := C)) := by
  apply Measurable.of_eval
  intro e
  exact measurable_pi_apply (⟨(e.1 : E), e.2⟩ : {e : E // e ∉ B.edges})

lemma measurable_inducedBoundary (α : C.BoundaryPartition) :
    Measurable (inducedBoundary N α) := by
  let F : ({e : C.graph.Edge // e ∉ N.ide} → Bool) → B.BoundaryPartition :=
    fun ξ => Setoid.comap N.vertEquiv.symm (exteriorPartition N.dom N.ide α ξ)
  have hF : Measurable F := measurable_of_finite _
  change Measurable (fun η => Setoid.comap N.vertEquiv.symm
    (exteriorPartition N.dom N.ide α (annulusOfExterior N η)))
  exact hF.comp (measurable_annulusOfExterior N)

/-- The small-box exterior generated by an exterior configuration of the large box
and one configuration of the annulus between the boxes. -/
noncomputable def nestedExterior (η : C.Exterior)
    (ξ : {e : C.graph.Edge // e ∉ N.ide} → Bool) : B.Exterior :=
  fun e => if h : (e.1 : E) ∈ C.edges then
    ξ ⟨⟨(e.1 : E), h⟩, e.2⟩ else η ⟨(e.1 : E), h⟩

lemma annulusOfExterior_nestedExterior (η : C.Exterior)
    (ξ : {e : C.graph.Edge // e ∉ N.ide} → Bool) :
    annulusOfExterior N (nestedExterior N η ξ) = ξ := by
  funext e
  simp [annulusOfExterior, nestedExterior, e.1.2]

lemma inducedBoundary_nestedExterior (α : C.BoundaryPartition) (η : C.Exterior)
    (ξ : {e : C.graph.Edge // e ∉ N.ide} → Bool) :
    inducedBoundary N α (nestedExterior N η ξ) =
      Setoid.comap N.vertEquiv.symm (exteriorPartition N.dom N.ide α ξ) := by
  simp [inducedBoundary, annulusOfExterior_nestedExterior]

lemma transportBoundary_inducedBoundary (α : C.BoundaryPartition) (η : B.Exterior) :
    transportBoundary N.vertEquiv N.edgeEquiv (inducedBoundary N α η) =
      exteriorPartition N.dom N.ide α (annulusOfExterior N η) := by
  apply Setoid.ext
  intro x y
  change (exteriorPartition N.dom N.ide α (annulusOfExterior N η)).r
    (N.vertEquiv.symm (N.vertEquiv x)) (N.vertEquiv.symm (N.vertEquiv y)) ↔ _
  rw [N.vertEquiv.symm_apply_apply x, N.vertEquiv.symm_apply_apply y]
  rfl

/-- Restriction of a small-box interior configuration to its realization in the
large box. -/
noncomputable def regionInterior (ζ : B.Interior) : ↥N.ide → Bool :=
  fun e => ζ (N.edgeEquiv e)

/-- Splitting a glued large-box configuration along the small box yields exactly
the nested exterior and the original small-box interior. -/
lemma split_glue_combine (η : C.Exterior) (ζ : B.Interior)
    (ξ : {e : C.graph.Edge // e ∉ N.ide} → Bool) :
    B.split (C.glue (η, combine N.ide (regionInterior N ζ) ξ)) =
      (nestedExterior N η ξ, ζ) := by
  apply Prod.ext
  · funext e
    by_cases hC : (e.1 : E) ∈ C.edges
    · have hB : (e.1 : E) ∉ B.edges := e.2
      change (C.glue (η, combine N.ide (regionInterior N ζ) ξ)) e.1 =
        nestedExterior N η ξ e
      simp only [FiniteBox.glue, nestedExterior, hC, dite_true]
      change combine N.ide (regionInterior N ζ) ξ ⟨(e.1 : E), hC⟩ =
        ξ ⟨⟨(e.1 : E), hC⟩, hB⟩
      rw [combine_of_not_mem N.ide _ _ ⟨⟨(e.1 : E), hC⟩, hB⟩]
    · change (C.glue (η, combine N.ide (regionInterior N ζ) ξ)) e.1 =
        nestedExterior N η ξ e
      simp only [FiniteBox.glue, nestedExterior, hC, dite_false]
  · funext e
    have hC : (e.1 : E) ∈ C.edges := N.edge_sub _ e.2
    have hid : (⟨(e.1 : E), hC⟩ : C.graph.Edge) ∈ N.ide := e.2
    change (C.glue (η, combine N.ide (regionInterior N ζ) ξ)) e.1 = ζ e
    simp only [FiniteBox.glue, hC, dite_true]
    change combine N.ide (regionInterior N ζ) ξ ⟨(e.1 : E), hC⟩ = ζ e
    rw [combine_of_mem N.ide _ _ ⟨⟨(e.1 : E), hC⟩, hid⟩]
    simp [regionInterior, NestedBox.edgeEquiv]

/-- The region sub-box law agrees with the transported small-box law for every
boundary partition, not merely for the free boundary. -/
lemma subBox_fkPMF_eq_transport_general (θ : Setoid N.dom) (ω : ↥N.ide → Bool) :
    (subBox N.dom N.ide N.hdom).fkPMF hq hp₁.le θ ω =
      (B.graph.transport N.vertEquiv N.edgeEquiv).fkPMF hq hp₁.le θ ω := by
  exact fkPMF_eq_of_source_target_eq
    (V := ↥N.dom) (E := ↥N.ide)
    (fun a => (⟨C.graph.source (a : C.graph.Edge), (N.hdom a).1⟩ : ↥N.dom))
    (fun a => (⟨C.graph.target (a : C.graph.Edge), (N.hdom a).2⟩ : ↥N.dom))
    (fun a => N.vertEquiv.symm (B.graph.source (N.edgeEquiv a)))
    (fun a => N.vertEquiv.symm (B.graph.target (N.edgeEquiv a)))
    N.transport_source_eq.symm N.transport_target_eq.symm hq hp₁.le _ ω

/-- Restriction of the region-level interior law to the small box has exactly
the induced-boundary FK law. -/
theorem map_transportConfig_subBox (α : C.BoundaryPartition) (η : B.Exterior) :
    PMF.map (B.graph.transportConfig N.vertEquiv N.edgeEquiv)
      ((subBox N.dom N.ide N.hdom).fkPMF hq hp₁.le
        (exteriorPartition N.dom N.ide α (annulusOfExterior N η))) =
      B.graph.fkPMF hq hp₁.le (inducedBoundary N α η) := by
  let θ : Setoid N.dom :=
    exteriorPartition (G := C.graph) N.dom N.ide α (annulusOfExterior N η)
  have hEq : (subBox (G := C.graph) N.dom N.ide N.hdom).fkPMF hq hp₁.le θ =
      (B.graph.transport N.vertEquiv N.edgeEquiv).fkPMF hq hp₁.le θ := by
    apply PMF.ext
    intro ω
    exact subBox_fkPMF_eq_transport_general (N := N) (hq := hq) (hp₁ := hp₁) θ ω
  change PMF.map (B.graph.transportConfig N.vertEquiv N.edgeEquiv)
    ((subBox (G := C.graph) N.dom N.ide N.hdom).fkPMF hq hp₁.le θ) = _
  rw [hEq]
  have hθ : θ = transportBoundary N.vertEquiv N.edgeEquiv (inducedBoundary N α η) := by
    exact (transportBoundary_inducedBoundary N α η).symm
  rw [hθ]
  exact map_transport_fkPMF B.graph N.vertEquiv N.edgeEquiv _ hq hp₁.le


/-- Transporting back to the small-box interior and then restricting to the
region is the identity. -/
lemma regionInterior_transportConfig (ζ : ↥N.ide → Bool) :
    regionInterior N (B.graph.transportConfig N.vertEquiv N.edgeEquiv ζ) = ζ := by
  funext e
  change ζ (N.edgeEquiv.symm (N.edgeEquiv e)) = ζ e
  rw [N.edgeEquiv.symm_apply_apply e]

/-- Region-interior form of `split_glue_combine`. -/
lemma split_glue_combine_region (η : C.Exterior) (ζ : ↥N.ide → Bool)
    (ξ : {e : C.graph.Edge // e ∉ N.ide} → Bool) :
    B.split (C.glue (η, combine N.ide ζ ξ)) =
      (nestedExterior N η ξ, B.graph.transportConfig N.vertEquiv N.edgeEquiv ζ) := by
  rw [← regionInterior_transportConfig N ζ]
  exact split_glue_combine N η _ ξ

include hq hp₀ hp₁

/-- The joint law induced by the nested finite mixture is the actual FK law. -/
lemma map_fibrePMF_nestedBox (α : C.BoundaryPartition) :
    PMF.map (fun z : (↥N.ide → Bool) × ({e : C.graph.Edge // e ∉ N.ide} → Bool) =>
        combine N.ide z.1 z.2)
      ((fibrePMF (G := C.graph) (I := N.ide) hq hp₁ α).bind fun ξ =>
        PMF.map (fun ζ => (ζ, ξ))
          ((subBox N.dom N.ide N.hdom).fkPMF hq hp₁.le
            (exteriorPartition N.dom N.ide α ξ))) =
      C.graph.fkPMF hq hp₁.le α :=
  map_fibrePMF_bind_subBox hq hp₀ hp₁ α

include hq hp₀ hp₁

/-- The nested large-box FK conditional law is DLR at the small box, with the
exact exterior-induced boundary partition.  This is the global comp-product
form of the source's finite specification identity. -/
theorem isDLR_conditionalLaw_nested (α : C.BoundaryPartition) (η : C.Exterior) :
    B.IsDLR hq hp₁.le (inducedBoundary N α) (measurable_inducedBoundary N α)
      (C.conditionalLaw hq hp₁.le (fun _ => α) η) := by
  let J : PMF ((↥N.ide → Bool) × ({e : C.graph.Edge // e ∉ N.ide} → Bool)) :=
    (fibrePMF (G := C.graph) (I := N.ide) hq hp₁ α).bind fun ξ =>
      PMF.map (fun ζ => (ζ, ξ))
        ((subBox N.dom N.ide N.hdom).fkPMF hq hp₁.le
          (exteriorPartition N.dom N.ide α ξ))
  let F : ((↥N.ide → Bool) × ({e : C.graph.Edge // e ∉ N.ide} → Bool)) →
      B.Exterior × B.Interior :=
    fun z => B.split (C.glue (η, combine N.ide z.1 z.2))
  let ν : PMF B.Exterior :=
    PMF.map (nestedExterior N η) (fibrePMF (G := C.graph) (I := N.ide) hq hp₁ α)
  have hPMF : PMF.map F J = ν.bind fun ηb =>
      PMF.map (Prod.mk ηb) (B.graph.fkPMF hq hp₁.le (inducedBoundary N α ηb)) := by
    dsimp only [J, F, ν]
    rw [PMF.map_bind, PMF.bind_map]
    apply congrArg (PMF.bind (fibrePMF (G := C.graph) (I := N.ide) hq hp₁ α))
    funext ξ
    change _ = PMF.map (Prod.mk (nestedExterior N η ξ))
      (B.graph.fkPMF hq hp₁.le (inducedBoundary N α (nestedExterior N η ξ)))
    rw [← map_transportConfig_subBox (N := N) (hq := hq) (hp₁ := hp₁) α (nestedExterior N η ξ)]
    rw [annulusOfExterior_nestedExterior]
    rw [PMF.map_comp]
    rw [PMF.map_comp (B.graph.transportConfig N.vertEquiv N.edgeEquiv)
      ((subBox N.dom N.ide N.hdom).fkPMF hq hp₁.le
        (exteriorPartition N.dom N.ide α ξ))
      (Prod.mk (nestedExterior N η ξ))]
    apply congrArg (fun f => PMF.map f
      ((subBox N.dom N.ide N.hdom).fkPMF hq hp₁.le
        (exteriorPartition N.dom N.ide α ξ)))
    funext ζ
    exact split_glue_combine_region N η ζ ξ
  have hFst : PMF.map Prod.fst (PMF.map F J) = ν := by
    rw [hPMF, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    have hmap (a : B.Exterior) (Q : PMF B.Interior) :
        PMF.map (fun _ : B.Interior => a) Q = PMF.pure a := by
      exact PMF.map_const Q a
    simp_rw [hmap]
    exact PMF.bind_pure ν
  have hcfk : C.graph.fkPMF hq hp₁.le α =
      PMF.map (fun z : (↥N.ide → Bool) × ({e : C.graph.Edge // e ∉ N.ide} → Bool) =>
        combine N.ide z.1 z.2) J := by
    exact (map_fibrePMF_nestedBox (N := N) (hq := hq) (hp₀ := hp₀) (hp₁ := hp₁) α).symm
  have hL : Measure.map B.splitEquiv
      (C.conditionalLaw hq hp₁.le (fun _ => α) η : Measure (Configuration E)) =
      (PMF.map F J).toMeasure := by
    change Measure.map B.splitEquiv
      (Measure.map (fun ξ : C.Interior => C.glue (η, ξ))
        (C.graph.fkMeasure hq hp₁.le α)) = _
    rw [Measure.map_map B.splitEquiv.measurable (C.measurable_glue_const_left η)]
    change Measure.map (B.splitEquiv ∘ fun ξ : C.Interior => C.glue (η, ξ))
      (C.graph.fkPMF hq hp₁.le α).toMeasure = _
    rw [hcfk, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
      Measure.map_map (B.splitEquiv.measurable.comp (C.measurable_glue_const_left η))
        (measurable_of_finite _)]
    exact PMF.toMeasure_map F J (measurable_of_finite _)
  have hext : (B.exteriorMeasure
      (C.conditionalLaw hq hp₁.le (fun _ => α) η) : Measure B.Exterior) =
      ν.toMeasure := by
    change Measure.map (Prod.fst ∘ B.splitEquiv)
      (C.conditionalLaw hq hp₁.le (fun _ => α) η : Measure (Configuration E)) = _
    rw [← Measure.map_map measurable_fst B.splitEquiv.measurable, hL,
      PMF.toMeasure_map _ _ measurable_fst]
    change (PMF.map Prod.fst (PMF.map F J)).toMeasure = _
    rw [hFst]
  rw [FiniteBox.IsDLR, hL, hext, hPMF]
  symm
  exact compProd_toMeasure_eq_toMeasure_bind ν
    (fun ηb => B.graph.fkPMF hq hp₁.le (inducedBoundary N α ηb))
    (B.interiorFKMeasure hq hp₁.le (inducedBoundary N α))
    (fun _ => rfl)
    (B.measurable_interiorFKMeasure hq hp₁.le _ (measurable_inducedBoundary N α))
    (fun ηb => FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      B.graph hq hp₁.le (inducedBoundary N α ηb))

/-- Closed-exterior specialization for an actual finite-volume FK law. -/
theorem isDLR_finiteVolumeLaw_nested (α : C.BoundaryPartition) :
    B.IsDLR hq hp₁.le (inducedBoundary N α) (measurable_inducedBoundary N α)
      (C.finiteVolumeLaw hq hp₁.le α) := by
  exact isDLR_conditionalLaw_nested (N := N) (hq := hq) (hp₀ := hp₀) (hp₁ := hp₁) α C.closedExterior



end NestedBoxDLR


end FK.NestedFinDLR
