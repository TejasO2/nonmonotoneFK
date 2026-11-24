import FK.PlanarActual
import FK.PlanarDLRDuality
import FK.FinitePlanarDuality

/-!
# Dual-parameter DLR transport for equation (12) of Theorem 1.11

The public `FK.InfiniteVolume.isDLR_map_cfgDual_of_pmf` transports the DLR
equation across a planar dual at a *single* parameter `(q,p)`.  The finite
conditioned duality of the source (equation (12), proved as
`FK.FinitePlane.equation_twelve_actual`) instead relates the primal law at
`(q,p)` to the dual law at the dual parameter `p* = q(1-p)/(p+q(1-p))`
(`FK.FinitePlane.dualParameter`), with `q` unchanged.

This module supplies the missing measure-theoretic half at those genuine
parameters, together with the two relabelling invariants needed to read the
`FiniteBox` PMF as the `interiorOfSum` PMF of the finite plane duality:

* edge-relabelling invariance of `edgeWeight`, `fkWeight`, `partitionFunction`
  and `fkPMF` for an arbitrary boundary partition
  (`FK.Finite.LabelledMultigraph.*_reindex`);
* the dual-parameter kernel/DLR transport and its dual-uniqueness corollary
  (`FK.InfiniteVolume.kernel_dual_of_pmf_dual_dualParameter`,
  `isDLR_map_cfgDual_dualParameter`, `eq_map_of_unique_dual_dualParameter`);
* the finite plane box over the global label type `I ⊕ O`
  (`FK.InfiniteVolume.planeBox`), the box-level form of equation (12)
  (`planeBox_pmf_dualParameter`), and the resulting transport and uniqueness
  theorems for the source's exterior-boundary conventions
  (`isDLR_map_cfgDual_equation_twelve`,
  `eq_map_of_unique_dual_equation_twelve`).

The only geometric input is the Euler component relation of the certified
plane-dual pair (`heuler`), exactly as in `equation_twelve_actual`.  No primal
at-most-one-cluster statement, planar embedding or infinite-volume conclusion is
asserted here, and the primal at-most-one cluster half of Theorem 1.11 remains
open.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open FK.FinitePlane FK.Configuration

local instance boundaryPartitionMeasurableSpaceDualParam (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

section relabel

namespace FK.Finite.LabelledMultigraph

universe u v

variable {V : Type u} (G : LabelledMultigraph.{u, v})

/-- The wired component count is invariant under relabelling the edges, for an
*arbitrary* boundary partition.  (The public `componentCount_reindex` is the
free-boundary case.) -/
lemma componentCount_reindex_apply {E' : Type v} [Fintype E'] (e : G.Edge ≃ E')
    (ξ : Setoid G.Vertex) (ω : E' → Bool) :
    (G.reindex e).componentCount ξ ω = G.componentCount ξ (fun a => ω (e a)) := by
  have hadj : ∀ x y,
      ((G.reindex e).connectionGraph ξ ω).Adj x y ↔
        (G.connectionGraph ξ (fun a => ω (e a))).Adj x y := by
    intro x y
    constructor
    · rintro ⟨hxy, h | ⟨a, ha, hJ⟩⟩
      · exact ⟨hxy, Or.inl h⟩
      · refine ⟨hxy, Or.inr ⟨e.symm (show E' from a), ?_,
          (joins_reindex G e (show E' from a) x y).mp hJ⟩⟩
        show ω (e (e.symm (show E' from a))) = true
        rw [Equiv.apply_symm_apply]
        exact ha
    · rintro ⟨hxy, h | ⟨b, hb, hJ⟩⟩
      · exact ⟨hxy, Or.inl h⟩
      · exact ⟨hxy, Or.inr ⟨e b, hb,
          (joins_reindex G e (e b) x y).mpr (by simpa using hJ)⟩⟩
  have hAdj : ((G.reindex e).connectionGraph ξ ω).Adj =
      (G.connectionGraph ξ (fun a => ω (e a))).Adj := by
    funext x y
    exact propext (hadj x y)
  have hgraph : (G.reindex e).connectionGraph ξ ω =
      G.connectionGraph ξ (fun a => ω (e a)) := SimpleGraph.ext hAdj
  show Nat.card ((G.reindex e).connectionGraph ξ ω).ConnectedComponent =
    Nat.card (G.connectionGraph ξ (fun a => ω (e a))).ConnectedComponent
  rw [hgraph]
  rfl

/-- The unnormalized edge weight is invariant under relabelling the edges. -/
lemma edgeWeight_reindex {E' : Type v} [Fintype E'] (e : G.Edge ≃ E')
    (p : NNReal) (ω : E' → Bool) :
    (G.reindex e).edgeWeight p ω = G.edgeWeight p (fun a => ω (e a)) := by
  classical
  show (∏ f : E', if ω f then p else 1 - p) =
    ∏ a : G.Edge, if ω (e a) then p else 1 - p
  exact (Fintype.prod_equiv e (fun a => if ω (e a) then p else 1 - p)
    (fun f => if ω f then p else 1 - p) (fun a => rfl)).symm

/-- The exact finite FK weight is invariant under relabelling the edges, for an
arbitrary boundary partition. -/
lemma fkWeight_reindex {E' : Type v} [Fintype E'] (e : G.Edge ≃ E')
    (q p : NNReal) (ξ : Setoid G.Vertex) (ω : E' → Bool) :
    (G.reindex e).fkWeight q p ξ ω = G.fkWeight q p ξ (fun a => ω (e a)) := by
  have hw : (G.reindex e).edgeWeight p ω = G.edgeWeight p (fun a => ω (e a)) :=
    edgeWeight_reindex G e p ω
  have hc : (G.reindex e).componentCount ξ ω = G.componentCount ξ (fun a => ω (e a)) :=
    componentCount_reindex_apply G e ξ ω
  show (G.reindex e).edgeWeight p ω * q ^ (G.reindex e).componentCount ξ ω =
    G.edgeWeight p (fun a => ω (e a)) * q ^ G.componentCount ξ (fun a => ω (e a))
  rw [hw, hc]

/-- The finite FK partition function is invariant under relabelling the edges. -/
lemma partitionFunction_reindex {E' : Type v} [Fintype E'] (e : G.Edge ≃ E')
    (q p : NNReal) (ξ : Setoid G.Vertex) :
    (G.reindex e).partitionFunction q p ξ = G.partitionFunction q p ξ := by
  classical
  have h : ∀ ω : E' → Bool,
      (G.reindex e).fkWeight q p ξ ω = G.fkWeight q p ξ (fun a => ω (e a)) :=
    fun ω => fkWeight_reindex G e q p ξ ω
  show (∑ ω : E' → Bool, (G.reindex e).fkWeight q p ξ ω) =
    ∑ ω : G.Edge → Bool, G.fkWeight q p ξ ω
  exact Fintype.sum_equiv (e.arrowCongr (Equiv.refl Bool)).symm _ _ h


/-- `normalizedPMFOfSumPos` is natural under an equivalence of the index types
that matches the weights. -/
lemma normalizedPMFOfSumPos_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (w : Ω → NNReal) (w' : Ω' → NNReal)
    (hw : ∀ a, w a = w' (e a))
    (hpos : 0 < ∑ a, w a) (hpos' : 0 < ∑ b, w' b) (a : Ω) :
    normalizedPMFOfSumPos w hpos a = normalizedPMFOfSumPos w' hpos' (e a) := by
  have hsum : (∑' b : Ω, ((w b : NNReal) : ℝ≥0∞)) =
      (∑' b : Ω', ((w' b : NNReal) : ℝ≥0∞)) := by
    rw [tsum_fintype, tsum_fintype]
    exact Fintype.sum_equiv e (fun b => ((w b : NNReal) : ℝ≥0∞))
      (fun b => ((w' b : NNReal) : ℝ≥0∞)) (fun b => by rw [hw b])
  rw [normalizedPMFOfSumPos_apply, normalizedPMFOfSumPos_apply, hw a, hsum]

/-- **Edge relabelling invariance of the normalized FK PMF.** -/
lemma fkPMF_reindex {E' : Type v} [Fintype E'] (e : G.Edge ≃ E')
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : Setoid G.Vertex)
    (ω : E' → Bool) :
    (G.reindex e).fkPMF hq hp ξ ω = G.fkPMF hq hp ξ (fun a => ω (e a)) := by
  classical
  have hw : ∀ ω : E' → Bool,
      (G.reindex e).fkWeight q p ξ ω = G.fkWeight q p ξ (fun a => ω (e a)) :=
    fun ω => fkWeight_reindex G e q p ξ ω
  have hsum : (∑ ω : E' → Bool, (G.reindex e).fkWeight q p ξ ω) =
      ∑ ω : G.Edge → Bool, G.fkWeight q p ξ ω :=
    partitionFunction_reindex G e q p ξ
  have htsum : (∑' b : E' → Bool, (((G.reindex e).fkWeight q p ξ b) : ℝ≥0∞)) =
      (∑' b : G.Edge → Bool, ((G.fkWeight q p ξ b) : ℝ≥0∞)) := by
    rw [tsum_fintype, tsum_fintype]
    calc (∑ b : E' → Bool, (((G.reindex e).fkWeight q p ξ b) : ℝ≥0∞))
        = ∑ b : E' → Bool, ((G.fkWeight q p ξ (fun a => b (e a))) : ℝ≥0∞) :=
          Finset.sum_congr rfl (fun b _ => by rw [hw b])
      _ = ∑ b : G.Edge → Bool, ((G.fkWeight q p ξ b) : ℝ≥0∞) :=
          Fintype.sum_equiv (e.arrowCongr (Equiv.refl Bool)).symm _ _
            (fun b => rfl)
  exact normalizedPMFOfSumPos_equiv (e.arrowCongr (Equiv.refl Bool)).symm
    ((G.reindex e).fkWeight q p ξ) (G.fkWeight q p ξ) (fun b => hw b) _ _ ω

end FK.Finite.LabelledMultigraph

end relabel

section dualparam

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Kernel identity at the dual parameter.**  If for every exterior
configuration the primal conditioned FK PMF at `(q,p)` equals the dual
conditioned FK PMF at `(q, p*)` composed with complementation, then the dual box
kernel at `(q,p*)` is the pushforward of the primal box kernel at `(q,p)` along
interior complementation.

This is `kernel_dual_of_pmf_dual` with the dual parameter `dualParameter q p`
in place of `p`; the hypothesis is exactly the conclusion of the finite
conditioned duality (equation (12)). -/
theorem kernel_dual_of_pmf_dual_dualParameter (B : FiniteBox E) (Vd : Type*)
    [Fintype Vd] (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq (FK.FinitePlane.dualParameter_le_one hq hp) (αD η)
          (intDual B ω)) :
    ∀ η : B.Exterior,
      (dualBox B Vd s t).fkKernel hq (FK.FinitePlane.dualParameter_le_one hq hp) αD hαD η =
        Measure.map (intDual B) (B.fkKernel hq hp α hα (extDual B η)) := by
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
  change (dualBox B Vd s t).graph.fkMeasure hq (FK.FinitePlane.dualParameter_le_one hq hp) (αD η) {ω} =
    B.graph.fkMeasure hq hp (α (extDual B η)) {intDual B ω}
  rw [FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton,
    FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]
  rw [hpmf η (intDual B ω), intDual_invol]

/-- **Duality transports the DLR equation to the dual parameters.**  If the
primal box FK kernels at `(q,p)` and the dual box FK kernels at `(q,p*)` are
related by complementing configurations --- the measure-level content of
equation (12) --- then complementing a `(q,p)`-DLR law of the primal box gives a
`(q,p*)`-DLR law of the dual box. -/
theorem isDLR_map_cfgDual_dualParameter (B : FiniteBox E) (Vd : Type*) [Fintype Vd]
    (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq (FK.FinitePlane.dualParameter_le_one hq hp) (αD η)
          (intDual B ω)) :
    (dualBox B Vd s t).IsDLR hq (FK.FinitePlane.dualParameter_le_one hq hp) αD hαD
      (ProbabilityMeasure.map μ (cfgDual E)) :=
  @isDLR_map_cfgDual_core E B q p hq hp α hα
    ((dualBox B Vd s t).fkKernel hq (FK.FinitePlane.dualParameter_le_one hq hp) αD hαD)
    (FiniteBox.fkKernel_isMarkov (B := dualBox B Vd s t) hq
      (FK.FinitePlane.dualParameter_le_one hq hp) αD hαD) μ hμ
    (kernel_dual_of_pmf_dual_dualParameter B Vd s t hq hp α hα αD hαD hpmf)

/-- **Dual uniqueness identifies the primal law at the dual parameters.**  This
is the final step of the duality argument of Theorem 1.11 with the paper's
parameters: if the dual box has a unique `(q,p*)`-DLR law `ν`, then every
`(q,p)`-DLR law of the primal box is the complement of `ν`. -/
theorem eq_map_of_unique_dual_dualParameter (B : FiniteBox E) (Vd : Type*)
    [Fintype Vd] (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq (FK.FinitePlane.dualParameter_le_one hq hp) (αD η)
          (intDual B ω))
    (_hν : (dualBox B Vd s t).IsDLR hq (FK.FinitePlane.dualParameter_le_one hq hp) αD hαD ν)
    (huniq : ∀ ν' : ProbabilityMeasure (Configuration E),
      (dualBox B Vd s t).IsDLR hq (FK.FinitePlane.dualParameter_le_one hq hp) αD hαD ν' → ν' = ν) :
    μ = ProbabilityMeasure.map ν (cfgDual E) := by
  have hdual := isDLR_map_cfgDual_dualParameter B Vd s t hq hp α hα αD hαD μ hμ hpmf
  have hkey : ProbabilityMeasure.map μ (cfgDual E) = ν := huniq _ hdual
  calc μ = ProbabilityMeasure.map (ProbabilityMeasure.map μ (cfgDual E)) (cfgDual E) :=
        (map_cfgDual_map_cfgDual μ).symm
    _ = ProbabilityMeasure.map ν (cfgDual E) := by rw [hkey]

/-! ## Relation to the paper's scalar parameter identity

The dual parameter is the one determined by `p/(1-p) * p*/(1-p*) = q`
(`FK.dual`), so the transported DLR class is indexed by the paper's `p*` and by
the *same* `q`.  The two public scalar facts used below are
`FK.prime_add_dual` (`p' + p* = 1`) and `FK.dual_mem_Icc`. -/

/-- The transported parameter is genuinely the paper's `p*`: it is the unique
`r ∈ [0,1]` with `FK.prime q p + r = 1`, i.e. the parameter complementary to the
singleton off-edge probability `p'`. -/
theorem coe_dualParameter_eq_one_sub_prime {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    (FK.FinitePlane.dualParameter q p : ℝ) = 1 - FK.prime (q : ℝ) (p : ℝ) := by
  rw [FK.FinitePlane.coe_dualParameter hq hp]
  exact FK.dual_eq_one_sub_prime (FK.denominator_ne_zero (by exact_mod_cast hq)
    (by positivity) (by exact_mod_cast hp))

end FK.InfiniteVolume

end dualparam

section planebox

namespace FK.InfiniteVolume

universe u

/-- The global edge-label set of the finite plane box: the interior labels `I`,
so that the complement is exactly the exterior labels `O`. -/
noncomputable def sumEdges (I O : Type*) [Fintype I] : Finset (I ⊕ O) := by
  classical
  exact Finset.univ.image Sum.inl

@[simp] lemma mem_sumEdges_inl (I O : Type*) [Fintype I] (i : I) :
    Sum.inl i ∈ sumEdges I O := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

@[simp] lemma not_mem_sumEdges_inr (I O : Type*) [Fintype I] (o : O) :
    Sum.inr o ∉ sumEdges I O := by
  classical
  simp only [sumEdges, Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨i, h⟩
  exact Sum.inl_ne_inr h

/-- The interior labels, identified with the box edges. -/
noncomputable def sumEdgesEquiv (I O : Type*) [Fintype I] : I ≃ ↥(sumEdges I O) :=
  Equiv.ofBijective (fun i => (⟨Sum.inl i, mem_sumEdges_inl I O i⟩ : ↥(sumEdges I O))) (by
    constructor
    · intro i j h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨e, he⟩
      classical
      simp only [sumEdges, Finset.mem_image, Finset.mem_univ, true_and] at he
      obtain ⟨i, rfl⟩ := he
      exact ⟨i, rfl⟩)

@[simp] lemma sumEdgesEquiv_apply (I O : Type*) [Fintype I] (i : I) :
    (sumEdgesEquiv I O i : I ⊕ O) = Sum.inl i := rfl

@[simp] lemma sumEdgesEquiv_symm_apply (I O : Type*) [Fintype I] (i : I) :
    (sumEdgesEquiv I O).symm ⟨Sum.inl i, mem_sumEdges_inl I O i⟩ = i := by
  have h1 : (sumEdgesEquiv I O)
      ((sumEdgesEquiv I O).symm ⟨Sum.inl i, mem_sumEdges_inl I O i⟩) =
      ⟨Sum.inl i, mem_sumEdges_inl I O i⟩ :=
    (sumEdgesEquiv I O).apply_symm_apply _
  have h2 : (sumEdgesEquiv I O) i = ⟨Sum.inl i, mem_sumEdges_inl I O i⟩ := rfl
  exact (sumEdgesEquiv I O).injective (h1.trans h2.symm)

universe w

variable {V VD I O OD : Type w} [Fintype V] [Fintype VD] [Fintype I] [Fintype O]
  [Fintype OD]

/-- The finite plane box over the global label type `I ⊕ O`, with interior edges
the `I`-labelled ones. -/
noncomputable def planeBox (s t : I ⊕ O → V) : FiniteBox (I ⊕ O) where
  Vertex := V
  edges := sumEdges I O
  source := fun e => s (Sum.inl ((sumEdgesEquiv I O).symm e))
  target := fun e => t (Sum.inl ((sumEdgesEquiv I O).symm e))

/-- The primal exterior configuration attached to a box exterior
configuration: read off the `O`-labelled coordinates. -/
noncomputable def planeExterior (s t : I ⊕ O → V) (η : (planeBox (V := V) s t).Exterior) :
    O → Bool :=
  fun o => η ⟨Sum.inr o, not_mem_sumEdges_inr I O o⟩

/-- The box graph is the interior FK graph of `interiorOfSum`, relabelled by
`sumEdgesEquiv`. -/
theorem planeBox_graph (s t : I ⊕ O → V) :
    (planeBox (V := V) s t).graph =
      (FK.FinitePlane.interiorOfSum s t).reindex (sumEdgesEquiv I O) := rfl

/-- **FK PMF of the plane box.**  It is the PMF of `interiorOfSum`, relabelled by
the canonical interior-label equivalence. -/
theorem planeBox_fkPMF (s t : I ⊕ O → V) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : Setoid V) (ω : (planeBox (V := V) s t).Interior) :
    (planeBox (V := V) s t).graph.fkPMF hq hp ξ ω =
      (FK.FinitePlane.interiorOfSum s t).fkPMF hq hp ξ
        (fun i => ω (sumEdgesEquiv I O i)) := by
  show ((FK.FinitePlane.interiorOfSum s t).reindex (sumEdgesEquiv I O)).fkPMF hq hp ξ ω =
    (FK.FinitePlane.interiorOfSum s t).fkPMF hq hp ξ (fun i => ω (sumEdgesEquiv I O i))
  exact FK.Finite.LabelledMultigraph.fkPMF_reindex
    (FK.FinitePlane.interiorOfSum s t) (sumEdgesEquiv I O) hq hp ξ ω

end FK.InfiniteVolume

end planebox

section eq12

namespace FK.InfiniteVolume

universe w

variable {V VD I O OD : Type w} [Fintype V] [Fintype VD] [Fintype I] [Fintype O]
  [Fintype OD]

/-- The primal boundary convention of the source: the exterior open-connected
component partition of the primal graph, read off the `O`-coordinates of the
box exterior configuration. -/
noncomputable def primalConvention (s t : I ⊕ O → V) :
    (planeBox (V := V) s t).Exterior → Setoid V :=
  fun η => exteriorBoundary s t (planeExterior s t η)

/-- The dual exterior configuration: the `OD`-coordinates of the box exterior
configuration, pulled back along the exterior label identification `eO`. -/
noncomputable def dualExterior (s t : I ⊕ O → V) (eO : O ≃ OD)
    (η : (planeBox (V := V) s t).Exterior) : OD → Bool :=
  fun od => η ⟨Sum.inr (eO.symm od), not_mem_sumEdges_inr I O (eO.symm od)⟩

/-- The dual boundary convention of the source: the exterior open-connected
component partition of the dual graph, read off the `OD`-coordinates. -/
noncomputable def dualConvention (s t : I ⊕ O → V) (sD tD : ↥(sumEdges I O) ⊕ OD → VD)
    (eO : O ≃ OD) (η : (planeBox (V := V) s t).Exterior) : Setoid VD :=
  exteriorBoundary sD tD (dualExterior s t eO η)

/-- Reading the exterior through `dualConfig` at a complemented exterior
configuration recovers the dual exterior coordinates. -/
lemma dualConfig_planeExterior (s t : I ⊕ O → V) (eO : O ≃ OD)
    (η : (planeBox (V := V) s t).Exterior) :
    dualConfig eO (fun o => !(planeExterior s t η o)) = dualExterior s t eO η := by
  funext od
  simp only [dualConfig, dualExterior, planeExterior, Equiv.symm_symm, Bool.not_not]

lemma measurable_primalConvention (s t : I ⊕ O → V) :
    Measurable (primalConvention (V := V) s t) :=
  measurable_of_finite _

lemma measurable_dualConvention (s t : I ⊕ O → V) (sD tD : ↥(sumEdges I O) ⊕ OD → VD)
    (eO : O ≃ OD) : Measurable (dualConvention (V := V) s t sD tD eO) :=
  measurable_of_finite _

/-- The interior complementation appearing in equation (12) is the box interior
complementation. -/
lemma dualConfig_comp_eq_intDual (s t : I ⊕ O → V)
    (ω : (planeBox (V := V) s t).Interior) :
    dualConfig (sumEdgesEquiv I O) (fun i => ω (sumEdgesEquiv I O i)) =
      intDual (planeBox (V := V) s t) ω := by
  funext a
  simp only [dualConfig, intDual_apply, Equiv.apply_symm_apply]

/-- The dual box graph is the interior dual graph of the sum decomposition. -/
theorem dualBox_planeBox_graph (s t : I ⊕ O → V)
    (sD tD : ↥(sumEdges I O) ⊕ OD → VD) :
    (dualBox (planeBox (V := V) s t) VD (fun e => sD (Sum.inl e))
      (fun e => tD (Sum.inl e))).graph = interiorOfSum sD tD := rfl

/-- **Equation (12) at the paper's parameters, in box language.**  For every
box exterior configuration the primal `(q,p)` conditioned FK PMF equals the dual
`(q,p*)` conditioned FK PMF composed with interior complementation. -/
theorem planeBox_pmf_dualParameter (s t : I ⊕ O → V)
    (sD tD : ↥(sumEdges I O) ⊕ OD → VD) (eO : O ≃ OD)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ : I ⊕ O → Bool,
      (ambientOfSum sD tD).componentCount (ambientOfSum sD tD).freeBoundary
          (dualConfig ((sumEdgesEquiv I O).sumCongr eO) ρ) + Fintype.card V =
        (ambientOfSum s t).componentCount (ambientOfSum s t).freeBoundary ρ +
          1 + openCard ρ) :
    ∀ (η : (planeBox (V := V) s t).Exterior) (ω : (planeBox (V := V) s t).Interior),
      (planeBox (V := V) s t).graph.fkPMF hq hp₁.le
          (primalConvention (V := V) s t
            (extDual (planeBox (V := V) s t) η)) ω =
        (dualBox (planeBox (V := V) s t) VD (fun e => sD (Sum.inl e))
            (fun e => tD (Sum.inl e))).graph.fkPMF hq
          (dualParameter_le_one hq hp₁.le) (dualConvention (V := V) s t sD tD eO η)
          (intDual (planeBox (V := V) s t) ω) := by
  intro η ω
  have hconv : primalConvention (V := V) s t
      (extDual (planeBox (V := V) s t) η) =
      exteriorBoundary s t (fun o => !(planeExterior s t η o)) := rfl
  rw [hconv]
  have h12 := equation_twelve_actual s t sD tD (sumEdgesEquiv I O) eO q p hq hp₀ hp₁
    heuler (fun o => !(planeExterior s t η o)) (fun i => ω (sumEdgesEquiv I O i))
  have hbox := planeBox_fkPMF (V := V) s t hq hp₁.le
    (exteriorBoundary s t (fun o => !(planeExterior s t η o))) ω
  have hbound : exteriorBoundary sD tD
      (dualConfig eO (fun o => !(planeExterior s t η o))) =
      exteriorBoundary sD tD (dualExterior s t eO η) := by
    rw [dualConfig_planeExterior]
  have hstep : (interiorOfSum sD tD).fkPMF hq (dualParameter_le_one hq hp₁.le)
      (exteriorBoundary sD tD (dualConfig eO (fun o => !(planeExterior s t η o))))
      (dualConfig (sumEdgesEquiv I O) (fun i => ω (sumEdgesEquiv I O i))) =
      (interiorOfSum sD tD).fkPMF hq (dualParameter_le_one hq hp₁.le)
        (exteriorBoundary sD tD (dualExterior s t eO η))
        (intDual (planeBox (V := V) s t) ω) := by
    exact Eq.trans
      (congrArg (fun Z => (interiorOfSum sD tD).fkPMF hq
        (dualParameter_le_one hq hp₁.le) Z
        (dualConfig (sumEdgesEquiv I O) (fun i => ω (sumEdgesEquiv I O i)))) hbound)
      (congrArg (fun f => (interiorOfSum sD tD).fkPMF hq
        (dualParameter_le_one hq hp₁.le)
        (exteriorBoundary sD tD (dualExterior s t eO η)) f)
        (dualConfig_comp_eq_intDual (V := V) s t ω))
  refine hbox.trans (h12.trans hstep)

/-- **Equation (12) gives the dual-parameter DLR transport.** -/
theorem isDLR_map_cfgDual_equation_twelve (s t : I ⊕ O → V)
    (sD tD : ↥(sumEdges I O) ⊕ OD → VD) (eO : O ≃ OD)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ : I ⊕ O → Bool,
      (ambientOfSum sD tD).componentCount (ambientOfSum sD tD).freeBoundary
          (dualConfig ((sumEdgesEquiv I O).sumCongr eO) ρ) + Fintype.card V =
        (ambientOfSum s t).componentCount (ambientOfSum s t).freeBoundary ρ +
          1 + openCard ρ)
    (hα : Measurable (primalConvention (V := V) s t))
    (hαD : Measurable (dualConvention (V := V) s t sD tD eO))
    (μ : ProbabilityMeasure (Configuration (I ⊕ O)))
    (hμ : (planeBox (V := V) s t).IsDLR hq hp₁.le (primalConvention (V := V) s t) hα μ) :
    (dualBox (planeBox (V := V) s t) VD (fun e => sD (Sum.inl e))
        (fun e => tD (Sum.inl e))).IsDLR hq (dualParameter_le_one hq hp₁.le)
      (dualConvention (V := V) s t sD tD eO) hαD
      (ProbabilityMeasure.map μ (cfgDual (I ⊕ O))) :=
  isDLR_map_cfgDual_dualParameter (planeBox (V := V) s t) VD
    (fun e => sD (Sum.inl e)) (fun e => tD (Sum.inl e)) hq hp₁.le
    (primalConvention (V := V) s t) hα (dualConvention (V := V) s t sD tD eO) hαD
    μ hμ (planeBox_pmf_dualParameter s t sD tD eO hq hp₀ hp₁ heuler)

/-- **Dual uniqueness identifies the primal law at the paper's parameters.**
If the dual box has a unique `(q,p*)`-DLR law `ν` for the source dual convention,
then every `(q,p)`-DLR law of the primal box is the complement of `ν`.  This is
the final step of the duality argument of Theorem 1.11. -/
theorem eq_map_of_unique_dual_equation_twelve (s t : I ⊕ O → V)
    (sD tD : ↥(sumEdges I O) ⊕ OD → VD) (eO : O ≃ OD)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ : I ⊕ O → Bool,
      (ambientOfSum sD tD).componentCount (ambientOfSum sD tD).freeBoundary
          (dualConfig ((sumEdgesEquiv I O).sumCongr eO) ρ) + Fintype.card V =
        (ambientOfSum s t).componentCount (ambientOfSum s t).freeBoundary ρ +
          1 + openCard ρ)
    (hα : Measurable (primalConvention (V := V) s t))
    (hαD : Measurable (dualConvention (V := V) s t sD tD eO))
    (μ ν : ProbabilityMeasure (Configuration (I ⊕ O)))
    (hμ : (planeBox (V := V) s t).IsDLR hq hp₁.le (primalConvention (V := V) s t) hα μ)
    (hν : (dualBox (planeBox (V := V) s t) VD (fun e => sD (Sum.inl e))
        (fun e => tD (Sum.inl e))).IsDLR hq (dualParameter_le_one hq hp₁.le)
      (dualConvention (V := V) s t sD tD eO) hαD ν)
    (huniq : ∀ ν' : ProbabilityMeasure (Configuration (I ⊕ O)),
      (dualBox (planeBox (V := V) s t) VD (fun e => sD (Sum.inl e))
          (fun e => tD (Sum.inl e))).IsDLR hq (dualParameter_le_one hq hp₁.le)
        (dualConvention (V := V) s t sD tD eO) hαD ν' → ν' = ν) :
    μ = ProbabilityMeasure.map ν (cfgDual (I ⊕ O)) :=
  eq_map_of_unique_dual_dualParameter (planeBox (V := V) s t) VD
    (fun e => sD (Sum.inl e)) (fun e => tD (Sum.inl e)) hq hp₁.le
    (primalConvention (V := V) s t) hα (dualConvention (V := V) s t sD tD eO) hαD
    μ ν hμ (planeBox_pmf_dualParameter s t sD tD eO hq hp₀ hp₁ heuler) hν huniq

end FK.InfiniteVolume

end eq12


/-! ## Axiom audit -/

#print axioms FK.Finite.LabelledMultigraph.componentCount_reindex_apply
#print axioms FK.Finite.LabelledMultigraph.edgeWeight_reindex
#print axioms FK.Finite.LabelledMultigraph.fkWeight_reindex
#print axioms FK.Finite.LabelledMultigraph.partitionFunction_reindex
#print axioms FK.Finite.LabelledMultigraph.normalizedPMFOfSumPos_equiv
#print axioms FK.Finite.LabelledMultigraph.fkPMF_reindex
#print axioms FK.InfiniteVolume.kernel_dual_of_pmf_dual_dualParameter
#print axioms FK.InfiniteVolume.isDLR_map_cfgDual_dualParameter
#print axioms FK.InfiniteVolume.eq_map_of_unique_dual_dualParameter
#print axioms FK.InfiniteVolume.coe_dualParameter_eq_one_sub_prime
#print axioms FK.InfiniteVolume.sumEdgesEquiv
#print axioms FK.InfiniteVolume.planeBox
#print axioms FK.InfiniteVolume.measurable_primalConvention
#print axioms FK.InfiniteVolume.measurable_dualConvention
#print axioms FK.InfiniteVolume.dualBox_planeBox_graph
#print axioms FK.InfiniteVolume.planeBox_fkPMF
#print axioms FK.InfiniteVolume.dualConfig_planeExterior
#print axioms FK.InfiniteVolume.dualConfig_comp_eq_intDual
#print axioms FK.InfiniteVolume.planeBox_pmf_dualParameter
#print axioms FK.InfiniteVolume.isDLR_map_cfgDual_equation_twelve
#print axioms FK.InfiniteVolume.eq_map_of_unique_dual_equation_twelve
