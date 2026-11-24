import FK.PlanarActual
import FK.InfiniteVolume

/-!
# Duality of the DLR equation for a box and its dual box

A finite box in this project is a finite labelled multigraph on a finite set of
*global* edge labels.  A planar dual pair shares the edge labels, so the same
set of labels is the interior of a primal box and of the dual box.  This file
proves the measure-theoretic half of the duality step in the proof of
Theorem 1.11 of Beffara--Faipeur--Oke (arXiv:2512.16486, Section 5.2): if the FK
box kernels of the primal and dual boxes are related by complementing
configurations, then complementing a DLR law of the primal box gives a DLR law
of the dual box.

The geometric half --- that a certified plane dual pair relates the two box
kernels in this way --- is the finite conditioned duality
`FK.FinitePlane.equation_twelve_actual`, whose Euler input is supplied by a
`GraphicDualCertificate`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## Edge relabelling invariance of the finite FK weights

A certified plane dual pair shares its edge labels, while a `FiniteBox` indexes
its interior edges by a `Finset` subtype.  These lemmas transport the wired
component count and the open-edge count across that relabelling; they are the
finite input needed to discharge the Euler hypothesis of
`FK.FinitePlane.equation_twelve_actual` from
`LabelledDualPair.componentCount_dual_add_card_vertices`. -/

namespace FK.Finite.LabelledMultigraph

universe u v

/-- Relabel the edges of a labelled multigraph along an equivalence. -/
def reindex (G : LabelledMultigraph.{u, v}) {E' : Type v} [Fintype E']
    (e : G.Edge ≃ E') : LabelledMultigraph.{u, v} where
  Vertex := G.Vertex
  Edge := E'
  source := fun a => G.source (e.symm a)
  target := fun a => G.target (e.symm a)

lemma joins_reindex (G : LabelledMultigraph.{u, v}) {E' : Type v} [Fintype E']
    (e : G.Edge ≃ E') (a : E') (x y : G.Vertex) :
    (G.reindex e).Joins a x y ↔ G.Joins (e.symm a) x y := Iff.rfl

/-- The wired component count is invariant under relabelling the edges. -/
lemma componentCount_reindex (G : LabelledMultigraph.{u, v}) {E' : Type v} [Fintype E']
    (e : G.Edge ≃ E') (ω : E' → Bool) :
    (G.reindex e).componentCount (G.reindex e).freeBoundary ω =
      G.componentCount G.freeBoundary (fun a => ω (e a)) := by
  have hadj : ∀ x y,
      ((G.reindex e).connectionGraph (G.reindex e).freeBoundary ω).Adj x y ↔
        (G.connectionGraph G.freeBoundary (fun a => ω (e a))).Adj x y := by
    intro x y
    simp only [FK.Finite.LabelledMultigraph.connectionGraph,
      FK.Finite.LabelledMultigraph.reindex, FK.Finite.LabelledMultigraph.Joins]
    constructor
    · rintro ⟨hxy, hrest⟩
      rcases hrest with h | ⟨a, ha, hJ⟩
      · exact absurd h hxy
      · exact ⟨hxy, Or.inr ⟨e.symm a, by simpa using ha, by simpa using hJ⟩⟩
    · rintro ⟨hxy, hrest⟩
      rcases hrest with h | ⟨b, hb, hJ⟩
      · exact absurd h hxy
      · refine ⟨hxy, Or.inr ⟨e b, by simpa using hb, ?_⟩⟩
        simpa using hJ
  have hAdj : ((G.reindex e).connectionGraph (G.reindex e).freeBoundary ω).Adj =
      (G.connectionGraph G.freeBoundary (fun a => ω (e a))).Adj := by
    funext x y
    exact propext (hadj x y)
  have hgraph : (G.reindex e).connectionGraph (G.reindex e).freeBoundary ω =
      G.connectionGraph G.freeBoundary (fun a => ω (e a)) := SimpleGraph.ext hAdj
  unfold FK.Finite.LabelledMultigraph.componentCount
  rw [hgraph]
  rfl

/-- The number of open edges is invariant under relabelling the edges. -/
lemma openCard_reindex (G : LabelledMultigraph.{u, v}) {E' : Type v} [Fintype E']
    (e : G.Edge ≃ E') (ω : E' → Bool) :
    FK.FinitePlane.openCard ω = FK.FinitePlane.openCard (fun a => ω (e a)) := by
  classical
  unfold FK.FinitePlane.openCard
  have himage : (Finset.univ.filter fun a : E' => ω a) =
      (Finset.univ.filter fun a : G.Edge => ω (e a)).image e := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ha
      exact ⟨e.symm a, by simpa using ha, by simp⟩
    · rintro ⟨b, hb, rfl⟩
      exact hb
  rw [himage, Finset.card_image_of_injective _ e.injective]

end FK.Finite.LabelledMultigraph

/-- The discrete measurable structure on boundary setoids, as in
`FK/InfiniteVolume.lean`. -/
local instance boundaryPartitionMeasurableSpace' (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

namespace FK.InfiniteVolume

variable {E : Type*}

/-- The box with the same global edge labels but with dual vertex/endpoint data.
It is reducible so that its exterior/interior configuration types are the
same as the primal box's types definitionally. -/
abbrev dualBox (B : FiniteBox E) (Vd : Type*) [Fintype Vd] (s t : B.edges → Vd) :
    FiniteBox E where
  Vertex := Vd
  edges := B.edges
  source := s
  target := t

/-- Pointwise complement on all global edge configurations. -/
def cfgDual (E : Type*) : Configuration E ≃ᵐ Configuration E :=
  FK.Configuration.dualMeasurableEquiv (Equiv.refl E)

/-- Pointwise complement on interior configurations of a box. -/
def intDual (B : FiniteBox E) : B.Interior ≃ᵐ B.Interior :=
  FK.Configuration.dualMeasurableEquiv (Equiv.refl B.edges)

/-- Pointwise complement on exterior configurations of a box. -/
def extDual (B : FiniteBox E) : B.Exterior ≃ᵐ B.Exterior :=
  FK.Configuration.dualMeasurableEquiv (Equiv.refl {e : E // e ∉ B.edges})

lemma intDual_apply (B : FiniteBox E) (ω : B.Interior) :
    intDual B ω = fun i => !(ω i) := by
  rw [intDual, FK.Configuration.dualMeasurableEquiv_apply]
  funext i; rfl

lemma extDual_apply (B : FiniteBox E) (η : B.Exterior) :
    extDual B η = fun i => !(η i) := by
  rw [extDual, FK.Configuration.dualMeasurableEquiv_apply]
  funext i; rfl

lemma cfgDual_apply (ω : Configuration E) : cfgDual E ω = fun e => !(ω e) := by
  rw [cfgDual, FK.Configuration.dualMeasurableEquiv_apply]
  funext e; rfl

lemma intDual_invol (B : FiniteBox E) (ω : B.Interior) : intDual B (intDual B ω) = ω := by
  rw [intDual_apply, intDual_apply]; funext i; simp

lemma extDual_invol (B : FiniteBox E) (η : B.Exterior) : extDual B (extDual B η) = η := by
  rw [extDual_apply, extDual_apply]; funext i; simp

lemma cfgDual_invol (ω : Configuration E) : cfgDual E (cfgDual E ω) = ω := by
  rw [cfgDual_apply, cfgDual_apply]; funext e; simp

lemma split_dualBox (B : FiniteBox E) (Vd : Type*) [Fintype Vd] (s t : B.edges → Vd) :
    (dualBox B Vd s t).split = B.split := rfl

/-- The canonical split intertwines global complementation with the two
coordinatewise complements. -/
lemma split_cfgDual (B : FiniteBox E) (ω : Configuration E) :
    B.split (cfgDual E ω) = (extDual B (B.split ω).1, intDual B (B.split ω).2) := by
  apply Prod.ext <;> funext i <;>
    simp [FiniteBox.split, cfgDual_apply, extDual_apply, intDual_apply]

/-- Comp-product with a Markov kernel at a singleton pair. -/
lemma compProd_singleton {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (ν : Measure α) [SFinite ν] (κ : Kernel α β) [IsSFiniteKernel κ]
    (a : α) (b : β) :
    (ν ⊗ₘ κ) {(a, b)} = ν {a} * κ a {b} := by
  have hset : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := Set.singleton_prod_singleton
  rw [← hset, Measure.compProd_apply_prod (measurableSet_singleton a)
    (measurableSet_singleton b), lintegral_singleton, mul_comm]

/-- Pushing a composition product forward along a product of measurable
equivalences transforms the second kernel accordingly. -/
lemma map_prod_map_compProd {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (e : α ≃ᵐ γ) (f : β ≃ᵐ δ) (ν : Measure α) [SFinite ν]
    (κ : Kernel α β) [IsSFiniteKernel κ] :
    Measure.map (Prod.map e f) (ν ⊗ₘ κ) =
      (Measure.map e ν) ⊗ₘ (Kernel.comap (κ.map (⇑f)) (⇑e.symm) e.symm.measurable) := by
  have hP : Measurable (Prod.map (⇑e) (⇑f)) :=
    (e.measurable.comp measurable_fst).prodMk (f.measurable.comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hP hs, Measure.compProd_apply hs,
    Measure.compProd_apply (hs.preimage hP),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) e.measurable]
  apply lintegral_congr
  intro x
  rw [Kernel.comap_apply, Kernel.map_apply (κ := κ) (f := ⇑f) f.measurable]
  simp only [MeasurableEquiv.symm_apply_apply]
  have hmap : (Measure.map (⇑f) (κ x)) (Prod.mk (e x) ⁻¹' s) =
      (κ x) (f ⁻¹' (Prod.mk (e x) ⁻¹' s)) :=
    Measure.map_apply f.measurable (hs.preimage (measurable_const.prodMk measurable_id))
  rw [hmap]
  rfl

/-- Singleton values of the exterior marginal are the primal law of the
exterior fibre. -/
lemma exteriorMeasure_apply_singleton [Countable E] (B : FiniteBox E)
    (μ : ProbabilityMeasure (Configuration E)) (η : B.Exterior) :
    (B.exteriorMeasure μ : Measure B.Exterior) {η} =
      (μ : Measure (Configuration E)) {ω | (B.split ω).1 = η} := by
  change (Measure.map (fun ω => (B.splitEquiv ω).1) (μ : Measure (Configuration E))) {η} = _
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton η)]
  congr 1

/-- The exterior marginal of a complemented law is the complemented exterior
marginal. -/
lemma exteriorMeasure_cfgDual (B : FiniteBox E) (μ : ProbabilityMeasure (Configuration E)) :
    (B.exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) : Measure B.Exterior) =
      Measure.map (extDual B) (B.exteriorMeasure μ : Measure B.Exterior) := by
  rw [show (B.exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) : Measure B.Exterior) =
      Measure.map (fun ω => (B.splitEquiv ω).1)
        (↑(ProbabilityMeasure.map μ (cfgDual E)) : Measure (Configuration E)) from rfl]
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map (by fun_prop) (cfgDual E).measurable]
  have hcomp : ((fun ω => (B.splitEquiv ω).1) ∘ (cfgDual E : Configuration E → Configuration E))
      = (extDual B) ∘ (fun ω => (B.splitEquiv ω).1) := by
    funext ω
    simp [FiniteBox.splitEquiv_apply, split_cfgDual]
  rw [hcomp, ← Measure.map_map (extDual B).measurable (by fun_prop)]
  rfl

end FK.InfiniteVolume

namespace FK.InfiniteVolume

variable {E : Type*}

lemma extDual_symm_eq (B : FiniteBox E) (η : B.Exterior) :
    (extDual B).symm η = extDual B η := by
  apply (extDual B).injective
  rw [(extDual B).apply_symm_apply, extDual_invol]

/-- **Duality transports the DLR equation (kernel form).**  If a Markov kernel
on the exterior is the pointwise complement of the FK box kernel, then
complementing a DLR law of the box gives the corresponding DLR identity with
that kernel. -/
theorem isDLR_map_cfgDual_core (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (κD : Kernel B.Exterior B.Interior) [IsMarkovKernel κD]
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hk : ∀ η : B.Exterior,
      κD η = Measure.map (intDual B) (B.fkKernel hq hp α hα (extDual B η))) :
    Measure.map B.splitEquiv
        (↑(ProbabilityMeasure.map μ (cfgDual E)) : Measure (Configuration E)) =
      (B.exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) : Measure B.Exterior) ⊗ₘ κD := by
  classical
  unfold FiniteBox.IsDLR at hμ
  have hsplit : ((B.splitEquiv : Configuration E → B.Exterior × B.Interior) ∘
        (cfgDual E : Configuration E → Configuration E)) =
      (Prod.map (extDual B) (intDual B) :
          B.Exterior × B.Interior → B.Exterior × B.Interior) ∘
        (B.splitEquiv : Configuration E → B.Exterior × B.Interior) := by
    funext ω
    simp only [Function.comp_apply, FiniteBox.splitEquiv_apply, split_cfgDual, Prod.map]
  have hP : Measurable (Prod.map (extDual B) (intDual B) :
      B.Exterior × B.Interior → B.Exterior × B.Interior) :=
    ((extDual B).measurable.comp measurable_fst).prodMk
      ((intDual B).measurable.comp measurable_snd)
  have hkey : Measure.map ((B.splitEquiv : Configuration E → B.Exterior × B.Interior) ∘
        (cfgDual E : Configuration E → Configuration E))
        (μ : Measure (Configuration E)) =
      Measure.map (Prod.map (extDual B) (intDual B))
        (Measure.map (B.splitEquiv : Configuration E → B.Exterior × B.Interior)
          (μ : Measure (Configuration E))) := by
    rw [hsplit, ← Measure.map_map hP B.splitEquiv.measurable]
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_map B.splitEquiv.measurable (cfgDual E).measurable, hkey, hμ,
    map_prod_map_compProd (extDual B) (intDual B), ← exteriorMeasure_cfgDual]
  congr 1
  apply Kernel.ext
  intro η
  rw [Kernel.comap_apply, Kernel.map_apply (κ := B.fkKernel hq hp α hα)
    (f := ⇑(intDual B)) (intDual B).measurable, extDual_symm_eq]
  exact (hk η).symm

/-- **Duality transports the DLR equation (dual-box form).**  If the FK box
kernels of a box and of its dual box (same global edge labels, dual endpoints)
are related by complementing configurations, then complementing a DLR law of
the box gives a DLR law of the dual box. -/
theorem isDLR_map_cfgDual (B : FiniteBox E) (Vd : Type*) [Fintype Vd]
    (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hk : ∀ η : B.Exterior,
      (dualBox B Vd s t).fkKernel hq hp αD hαD η
        = Measure.map (intDual B) (B.fkKernel hq hp α hα (extDual B η))) :
    (dualBox B Vd s t).IsDLR hq hp αD hαD (ProbabilityMeasure.map μ (cfgDual E)) := by
  exact @isDLR_map_cfgDual_core E B q p hq hp α hα
    ((dualBox B Vd s t).fkKernel hq hp αD hαD)
    (FiniteBox.fkKernel_isMarkov (B := dualBox B Vd s t) hq hp αD hαD) μ hμ hk


/-- The finite conditioned duality of equation (12), stated as a pointwise
identity of normalized FK PMFs, gives the kernel duality hypothesis. -/
theorem kernel_dual_of_pmf_dual (B : FiniteBox E) (Vd : Type*) [Fintype Vd]
    (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq hp (αD η) (intDual B ω)) :
    ∀ η : B.Exterior,
      (dualBox B Vd s t).fkKernel hq hp αD hαD η
        = Measure.map (intDual B) (B.fkKernel hq hp α hα (extDual B η)) := by
  intro η
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.map_apply (intDual B).measurable (measurableSet_singleton ω)]
  have hpre : ((intDual B) ⁻¹' {ω} : Set B.Interior) = {intDual B ω} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, intDual_invol]
    · intro h
      rw [h, intDual_invol]
  rw [hpre]
  change (dualBox B Vd s t).graph.fkMeasure hq hp (αD η) {ω} =
    B.graph.fkMeasure hq hp (α (extDual B η)) {intDual B ω}
  rw [FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton,
    FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]
  rw [hpmf η (intDual B ω), intDual_invol]

/-- **Duality transports the DLR equation, from finite conditioned duality.**
If normalized FK PMFs of a box and its dual box are related by complementation
of configurations for every exterior configuration --- which is the finite
content of equation (12) --- then complementing a DLR law of the box gives a
DLR law of the dual box. -/
theorem isDLR_map_cfgDual_of_pmf (B : FiniteBox E) (Vd : Type*) [Fintype Vd]
    (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq hp (αD η) (intDual B ω)) :
    (dualBox B Vd s t).IsDLR hq hp αD hαD (ProbabilityMeasure.map μ (cfgDual E)) :=
  isDLR_map_cfgDual B Vd s t hq hp α hα αD hαD μ hμ
    (kernel_dual_of_pmf_dual B Vd s t hq hp α hα αD hαD hpmf)

/-- Complementation is an involution on probability laws. -/
lemma map_cfgDual_map_cfgDual (μ : ProbabilityMeasure (Configuration E)) :
    ProbabilityMeasure.map (ProbabilityMeasure.map μ (cfgDual E)) (cfgDual E) = μ := by
  apply Subtype.ext
  show Measure.map (cfgDual E) (Measure.map (cfgDual E) (μ : Measure (Configuration E)))
    = (μ : Measure (Configuration E))
  rw [Measure.map_map (cfgDual E).measurable (cfgDual E).measurable]
  have hfun : ((cfgDual E) ∘ (cfgDual E) : Configuration E → Configuration E) = id := by
    funext ω
    exact cfgDual_invol ω
  rw [hfun, Measure.map_id]

/-- **Dual uniqueness identifies the primal law.**  This is the final step of
the proof of Theorem 1.11: if the dual box has a unique DLR law `ν`, then every
DLR law of the primal box is the complement of `ν`. -/
theorem eq_map_of_unique_dual (B : FiniteBox E) (Vd : Type*) [Fintype Vd]
    (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq hp (αD η) (intDual B ω))
    (_hν : (dualBox B Vd s t).IsDLR hq hp αD hαD ν)
    (huniq : ∀ ν' : ProbabilityMeasure (Configuration E),
      (dualBox B Vd s t).IsDLR hq hp αD hαD ν' → ν' = ν) :
    μ = ProbabilityMeasure.map ν (cfgDual E) := by
  have hdual := isDLR_map_cfgDual_of_pmf B Vd s t hq hp α hα αD hαD μ hμ hpmf
  have hkey : ProbabilityMeasure.map μ (cfgDual E) = ν := huniq _ hdual
  calc μ = ProbabilityMeasure.map (ProbabilityMeasure.map μ (cfgDual E)) (cfgDual E) :=
        (map_cfgDual_map_cfgDual μ).symm
    _ = ProbabilityMeasure.map ν (cfgDual E) := by rw [hkey]

/-! ## Axiom audit -/

#print axioms FK.InfiniteVolume.isDLR_map_cfgDual_core
#print axioms FK.InfiniteVolume.isDLR_map_cfgDual
#print axioms FK.InfiniteVolume.isDLR_map_cfgDual_of_pmf
#print axioms FK.InfiniteVolume.eq_map_of_unique_dual

end FK.InfiniteVolume
