import FK.NoncoherentCounterexample
import FK.Theorem110GeomFamily

/-!
# Scope calibration: the unrestricted FK family is not the paper's family

Stage 21, direction 8 (`m1`, swarm `smwu4rrf3`).

`FK.InfiniteVolume.FKFamily` is the union of *all* measurable boundary-convention
DLR classes with the class of FK weak limits
(`docs/THEOREM110-ASSEMBLY.md` §1.2).  It is used in
`theorem_1_10_modulo_theorem_5_1` as if it were the paper's family
`⋃_Φ 𝒢^Φ ∪ 𝒲` of arXiv:2512.16486v1, on the grounds that allowing more
conventions only makes the statement stronger.

This file proves that this reading is **false**: on the two-vertex graph with a
single edge, at `q = 1/2 < 1` and `p = 1/2`, the class of FK weak limits — hence
the total family — has at least two distinct members.  The two members are the
limits of the constant *free*-boundary and constant *wired*-boundary sequences;
the wired boundary setoid is not induced by any exterior configuration of this
exhaustion (there are no exterior edges at all), so it is not one of the
paper's boundary conditions.

Consequently:

* no statement of the shape `∃! μ, μ ∈ FKFamily exh hq hp` can hold for the
  unrestricted family, independently of any percolation input;
* the hypotheses `h5_1`/`h518` of `theorem_1_10_modulo_inputs` are not
  bookkeeping: `h518` fails for the free convention on this example
  (`wiredOneEdgeLimit_not_mem_free_dlr`);
* a source-faithful Theorem 1.10 must restrict the convention family to
  geometrically realizable boundary assignments (`IsGeometric`), which is the
  scope correction recorded in `docs/THEOREM110-STRASSEN.md`.

The numbers are exact: with `p = q = 1/2` the free law gives the unique edge
mass `2/3` and the wired law gives `1/2`.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.Scope

open FK.Finite FK.Finite.LabelledMultigraph
open FK.InfiniteVolume.NoncoherentCounterexample
open FK.InfiniteVolume.ConventionTransport

noncomputable section

/-- The graph's own `Fintype` instance for the configuration type, with high
priority so that sums over configurations use the same instance as
`LabelledMultigraph.partitionFunction`. -/
local instance oneEdgeConfigurationFintype : Fintype oneEdgeBox.graph.Configuration :=
  oneEdgeBox.graph.instFintypeConfiguration

/-! ## The one-edge weights at `p = q = 1/2` -/

lemma oneEdge_free_weight_allOpen_half :
    oneEdgeBox.graph.fkWeight (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.freeBoundary oneEdgeBox.graph.allOpen = 1 / 4 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    oneEdge_componentCount_free_allOpen, LabelledMultigraph.allOpen]

lemma oneEdge_free_weight_allClosed_half :
    oneEdgeBox.graph.fkWeight (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.freeBoundary oneEdgeBox.graph.allClosed = 1 / 8 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    oneEdge_componentCount_free_allClosed, LabelledMultigraph.allClosed, oneEdgeBox,
    oneHalf_sub_oneHalf]

lemma oneEdge_wired_weight_allOpen_half :
    oneEdgeBox.graph.fkWeight (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.wiredBoundary oneEdgeBox.graph.allOpen = 1 / 4 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    LabelledMultigraph.allOpen, componentCount_wired]

lemma oneEdge_wired_weight_allClosed_half :
    oneEdgeBox.graph.fkWeight (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.wiredBoundary oneEdgeBox.graph.allClosed = 1 / 4 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    LabelledMultigraph.allClosed, componentCount_wired, oneHalf_sub_oneHalf]

lemma oneEdge_free_partitionFunction_half :
    oneEdgeBox.graph.partitionFunction (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.freeBoundary = 3 / 8 := by
  let f : oneEdgeBox.graph.Configuration → NNReal := fun ω =>
    oneEdgeBox.graph.fkWeight (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.freeBoundary ω
  have hsum : (∑ ω, f ω) = f oneEdgeBox.graph.allOpen + f oneEdgeBox.graph.allClosed :=
    sum_oneEdgeConfiguration f
  unfold LabelledMultigraph.partitionFunction
  exact hsum.trans (by
    dsimp [f]
    rw [oneEdge_free_weight_allOpen_half, oneEdge_free_weight_allClosed_half]
    norm_num)

lemma oneEdge_wired_partitionFunction_half :
    oneEdgeBox.graph.partitionFunction (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.wiredBoundary = 1 / 2 := by
  let f : oneEdgeBox.graph.Configuration → NNReal := fun ω =>
    oneEdgeBox.graph.fkWeight (1 / 2 : NNReal) (1 / 2 : NNReal)
      oneEdgeBox.graph.wiredBoundary ω
  have hsum : (∑ ω, f ω) = f oneEdgeBox.graph.allOpen + f oneEdgeBox.graph.allClosed :=
    sum_oneEdgeConfiguration f
  unfold LabelledMultigraph.partitionFunction
  exact hsum.trans (by
    dsimp [f]
    rw [oneEdge_wired_weight_allOpen_half, oneEdge_wired_weight_allClosed_half]
    norm_num)

lemma oneEdge_free_allOpen_mass_half :
    oneEdgeBox.graph.fkPMF (q := 1 / 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary
        oneEdgeBox.graph.allOpen = (2 / 3 : NNReal) := by
  rw [LabelledMultigraph.fkPMF_apply, oneEdge_free_weight_allOpen_half,
    oneEdge_free_partitionFunction_half]
  norm_num

lemma oneEdge_wired_allOpen_mass_half :
    oneEdgeBox.graph.fkPMF (q := 1 / 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary
        oneEdgeBox.graph.allOpen = (1 / 2 : NNReal) := by
  rw [LabelledMultigraph.fkPMF_apply, oneEdge_wired_weight_allOpen_half,
    oneEdge_wired_partitionFunction_half]
  norm_num

/-- At `p = q = 1/2` the free and wired finite FK laws on the one-edge box are
distinct: the all-open mass is `2/3` against `1/2`. -/
lemma oneEdge_free_fkMeasure_ne_wired_half :
    oneEdgeBox.graph.fkMeasure (q := 1 / 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary ≠
    oneEdgeBox.graph.fkMeasure (q := 1 / 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary := by
  intro h
  have hm := congrArg (fun ν : Measure oneEdgeBox.Interior =>
    ν {oneEdgeBox.graph.allOpen}) h
  simp only [LabelledMultigraph.fkMeasure,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    oneEdge_free_allOpen_mass_half, oneEdge_wired_allOpen_mass_half] at hm
  have h23 : (2 / 3 : NNReal) = 1 / 2 := ENNReal.coe_injective hm
  norm_num at h23

end

/-! ## The two constant-boundary limits of the one-edge exhaustion -/

section Limits

/-- The free constant-boundary finite-volume limit on the one-edge exhaustion. -/
noncomputable def freeOneEdgeLimit :
    ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet) :=
  oneEdgeBox.finiteVolumeLaw (q := 1 / 2) (p := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary

/-- The wired constant-boundary finite-volume limit on the one-edge exhaustion. -/
noncomputable def wiredOneEdgeLimitHalf :
    ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet) :=
  oneEdgeBox.finiteVolumeLaw (q := 1 / 2) (p := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary

theorem isFKLimit_freeOneEdgeLimit :
    IsFKLimit oneEdgeExhaustion (q := 1 / 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num)
      (fun _ => oneEdgeBox.graph.freeBoundary) freeOneEdgeLimit :=
  tendsto_const_nhds

theorem isFKLimit_wiredOneEdgeLimitHalf :
    IsFKLimit oneEdgeExhaustion (q := 1 / 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num)
      (fun _ => oneEdgeBox.graph.wiredBoundary) wiredOneEdgeLimitHalf :=
  tendsto_const_nhds

/-- The free and wired constant-boundary limits differ, because their interior
restrictions are the free and wired FK laws on the one-edge box. -/
theorem freeOneEdgeLimit_ne_wiredOneEdgeLimitHalf :
    freeOneEdgeLimit ≠ wiredOneEdgeLimitHalf := by
  intro h
  apply oneEdge_free_fkMeasure_ne_wired_half
  have hm := congrArg (fun μ : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet) =>
    Measure.map oneEdgeBox.interiorRestriction
      (μ : Measure (Configuration TwoVertexGraph.edgeSet))) h
  simpa [freeOneEdgeLimit, wiredOneEdgeLimitHalf, FiniteBox.finiteVolumeLaw,
    oneEdgeBox.map_interiorRestriction_conditionalLaw] using hm

end Limits

/-! ## The unrestricted family is not a singleton -/

section NonUniqueness

/-- **The class of FK weak limits on the one-edge exhaustion has at least two
elements** at `q = p = 1/2`: the free and wired constant-boundary limits. -/
theorem fkLimitMeasures_oneEdge_not_existsUnique :
    ¬ ∃! μ : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet),
        μ ∈ FKLimitMeasures oneEdgeExhaustion (q := 1 / 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) := by
  rintro ⟨μ, -, huniq⟩
  have hf : freeOneEdgeLimit ∈ FKLimitMeasures oneEdgeExhaustion
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
    ⟨fun _ => oneEdgeBox.graph.freeBoundary, isFKLimit_freeOneEdgeLimit⟩
  have hw : wiredOneEdgeLimitHalf ∈ FKLimitMeasures oneEdgeExhaustion
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
    ⟨fun _ => oneEdgeBox.graph.wiredBoundary, isFKLimit_wiredOneEdgeLimitHalf⟩
  exact freeOneEdgeLimit_ne_wiredOneEdgeLimitHalf (by rw [huniq _ hf, huniq _ hw])

/-- **The total FK family on the one-edge exhaustion is not a singleton** at
`q = p = 1/2`.

Consequently the paper's Theorem 1.10 conclusion `∃! μ, μ ∈ FKFamily ...
cannot be stated for the unrestricted union over all measurable boundary
assignments: the two members are produced by boundary setoids indiscriminately,
one of which (the fully wired one) is not induced by any exterior configuration
of this exhaustion. -/
theorem fkFamily_oneEdge_not_existsUnique :
    ¬ ∃! μ : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet),
        μ ∈ FKFamily oneEdgeExhaustion (q := 1 / 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) := by
  rintro ⟨μ, -, huniq⟩
  have hf : freeOneEdgeLimit ∈ FKFamily oneEdgeExhaustion
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
    mem_fkFamily_of_mem_fkLimit (by norm_num) (by norm_num) oneEdgeExhaustion
      ⟨fun _ => oneEdgeBox.graph.freeBoundary, isFKLimit_freeOneEdgeLimit⟩
  have hw : wiredOneEdgeLimitHalf ∈ FKFamily oneEdgeExhaustion
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
    mem_fkFamily_of_mem_fkLimit (by norm_num) (by norm_num) oneEdgeExhaustion
      ⟨fun _ => oneEdgeBox.graph.wiredBoundary, isFKLimit_wiredOneEdgeLimitHalf⟩
  exact freeOneEdgeLimit_ne_wiredOneEdgeLimitHalf (by rw [huniq _ hf, huniq _ hw])

/-- The same failure for the exhaustion-independent total family. -/
theorem fkFamilyAll_oneEdge_not_existsUnique :
    ¬ ∃! μ : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet),
        μ ∈ FKFamilyAll (G := TwoVertexGraph) (q := 1 / 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) := by
  rintro ⟨μ, -, huniq⟩
  have hf : freeOneEdgeLimit ∈ FKFamilyAll (G := TwoVertexGraph)
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
    mem_fkFamilyAll_of_mem_fkFamily (by norm_num) (by norm_num) oneEdgeExhaustion
      (mem_fkFamily_of_mem_fkLimit (by norm_num) (by norm_num) oneEdgeExhaustion
        ⟨fun _ => oneEdgeBox.graph.freeBoundary, isFKLimit_freeOneEdgeLimit⟩)
  have hw : wiredOneEdgeLimitHalf ∈ FKFamilyAll (G := TwoVertexGraph)
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
    mem_fkFamilyAll_of_mem_fkFamily (by norm_num) (by norm_num) oneEdgeExhaustion
      (mem_fkFamily_of_mem_fkLimit (by norm_num) (by norm_num) oneEdgeExhaustion
        ⟨fun _ => oneEdgeBox.graph.wiredBoundary, isFKLimit_wiredOneEdgeLimitHalf⟩)
  exact freeOneEdgeLimit_ne_wiredOneEdgeLimitHalf (by rw [huniq _ hf, huniq _ hw])

end NonUniqueness

/-! ## The two-vertex graph has critical probability one -/

section Criticality

open CurvatureVariance.Infra.Percolation

/-- On the two-vertex graph every open cluster is finite, so every Bernoulli
percolation law is a.s. non-percolating. -/
theorem percolationProb_twoVertex_eq_zero (o : Bool) (p : unitInterval) :
    percolationProb TwoVertexGraph o p = 0 := by
  unfold percolationProb
  have hempty : {S : Set TwoVertexGraph.edgeSet |
      {x | (openGraph TwoVertexGraph S).Reachable o x}.Infinite} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro S h
    exact h (Set.toFinite _)
  rw [hempty, measure_empty]

/-- `p_c = 1` on the two-vertex graph.  Hence every `p < 1`, and in particular
`p = 1/2`, lies in the subcritical range in which the paper's Theorem 1.10 is
supposed to apply. -/
theorem criticalProb_twoVertex (o : Bool) : criticalProb TwoVertexGraph o = 1 := by
  unfold criticalProb
  have hset : Subtype.val '' {p : unitInterval |
      percolationProb TwoVertexGraph o p = 0} = Set.Icc (0 : ℝ) 1 := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨p, -, rfl⟩
      exact ⟨p.2.1, p.2.2⟩
    · intro x hx
      exact ⟨⟨x, hx⟩, percolationProb_twoVertex_eq_zero o ⟨x, hx⟩, rfl⟩
  rw [hset, csSup_Icc zero_le_one]

end Criticality

/-! ## The wired convention is not geometrically realizable -/

section Geometry

/-- The constant wired boundary assignment on the one-edge exhaustion. -/
def wiredConstantAssignment : BoundaryAssignment oneEdgeExhaustion.box where
  partition := fun _ _ => oneEdgeBox.graph.wiredBoundary
  measurable_partition := fun _ => measurable_const

/-- **No geometric convention of the one-edge exhaustion is the wired one.**

The exhaustion has a single exterior configuration, and every box edge is
closed in it, so all exterior open components are singletons and no exterior
cluster is infinite.  A geometric assignment must therefore coincide with the
free (discrete) partition, while the wired assignment identifies the two
vertices. -/
theorem not_isGeometric_wiredConstantAssignment :
    ¬ IsGeometric oneEdgeBoxData.geometry wiredConstantAssignment := by
  intro hgeo
  have hcomp : oneEdgeBoxData.geometry.components 0 oneEdgeBox.closedExterior
      = oneEdgeBox.graph.freeBoundary :=
    oneEdge_free_partition oneEdgeBox.closedExterior
  have hnotC : ¬ (oneEdgeBoxData.geometry.components 0 oneEdgeBox.closedExterior).r
      false true := by
    rw [hcomp]
    exact fun h => Bool.noConfusion h
  have hnotInf : ¬ oneEdgeBoxData.geometry.infinite 0 oneEdgeBox.closedExterior true := by
    intro h
    exact h (Set.toFinite _)
  have hsep := (hgeo.2 0 oneEdgeBox.closedExterior) hnotC (Or.inr hnotInf)
  exact hsep trivial

end Geometry

/-! ## The geometric restriction repairs the failure

The unrestricted family has two members on the one-edge exhaustion.  Here we
show that the *geometrically realizable* family of `FKFamilyGeom` does not
contain the spurious wired member: every geometric convention of this
exhaustion is the free one, hence so is every geometric weak limit. -/

section GeometricRepair

/-- **Every geometric convention of the one-edge exhaustion is the free
partition.**  There is a single exterior configuration, its box edges are all
closed, so the exterior components are singletons and no exterior cluster is
infinite; separation of finite components then forces the partition to be
discrete. -/
theorem geometric_partition_eq_free (Φ : BoundaryAssignment oneEdgeExhaustion.box)
    (hΦ : IsGeometric oneEdgeBoxData.geometry Φ) (n : ℕ)
    (η : (oneEdgeExhaustion.box n).Exterior) :
    Φ.partition n η = oneEdgeBox.graph.freeBoundary := by
  have hcomp : oneEdgeBoxData.geometry.components n η = oneEdgeBox.graph.freeBoundary :=
    oneEdge_free_partition η
  have hmerge := hΦ.1 n η
  have hsep : ∀ {x y : (oneEdgeExhaustion.box n).Vertex},
      ¬(oneEdgeBoxData.geometry.components n η).r x y →
        (¬oneEdgeBoxData.geometry.infinite n η x ∨
          ¬oneEdgeBoxData.geometry.infinite n η y) →
        ¬(Φ.partition n η).r x y :=
    fun {x y} => hΦ.2 n η (x := x) (y := y)
  apply Setoid.ext
  intro x y
  constructor
  · intro hxy
    by_contra hne
    have hnotC : ¬ (oneEdgeBoxData.geometry.components n η).r x y := by
      rw [hcomp]
      exact hne
    have hnotInf : ¬ oneEdgeBoxData.geometry.infinite n η x ∨
        ¬ oneEdgeBoxData.geometry.infinite n η y :=
      Or.inl fun h => h (Set.toFinite _)
    exact hsep hnotC hnotInf hxy
  · intro hxy
    have hxyeq : x = y := hxy
    subst y
    exact (Φ.partition n η).iseqv.refl x

/-- Every geometric weak limit on the one-edge exhaustion is the free limit: the
finite-volume law at every box is the free one. -/
theorem isGeometricFKLimit_eq_freeOneEdgeLimit
    {μ : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet)}
    (hμ : IsGeometricFKLimit oneEdgeExhaustion oneEdgeBoxData
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) μ) :
    μ = freeOneEdgeLimit := by
  obtain ⟨Φ, η, hlim⟩ := hμ
  have hconst : (fun n => (oneEdgeExhaustion.box n).finiteVolumeLaw
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      (Φ.1.partition n (η n))) = fun _ => freeOneEdgeLimit := by
    funext n
    rw [geometric_partition_eq_free Φ.1 Φ.2 n (η n)]
    rfl
  have hlim' : Tendsto (fun n => (oneEdgeExhaustion.box n).finiteVolumeLaw
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      (Φ.1.partition n (η n))) atTop (𝓝 μ) := hlim
  rw [hconst] at hlim'
  exact (tendsto_const_nhds_iff.mp hlim').symm

/-- **The wired member is excluded by the geometric family.** -/
theorem wiredOneEdgeLimitHalf_not_mem_fkFamilyGeom :
    wiredOneEdgeLimitHalf ∉ FKFamilyGeom oneEdgeExhaustion oneEdgeBoxData
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) := by
  intro hmem
  rcases hmem with hmem | hmem
  · obtain ⟨Φ, hΦ⟩ := Set.mem_iUnion.mp hmem
    have hD := hΦ 0
    have hd := map_interiorRestriction_of_isDLR_of_subsingleton oneEdgeBox
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      (Φ.1.partition 0) (Φ.1.measurable_partition 0) wiredOneEdgeLimitHalf hD
    have hw : Measure.map oneEdgeBox.interiorRestriction
        (wiredOneEdgeLimitHalf : Measure (Configuration TwoVertexGraph.edgeSet)) =
        oneEdgeBox.graph.fkMeasure (q := 1 / 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary := by
      simpa [wiredOneEdgeLimitHalf, FiniteBox.finiteVolumeLaw] using
        oneEdgeBox.map_interiorRestriction_conditionalLaw
          (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
          (fun _ => oneEdgeBox.graph.wiredBoundary) oneEdgeBox.closedExterior
    rw [hw, geometric_partition_eq_free Φ.1 Φ.2 0
      (default : oneEdgeBox.Exterior)] at hd
    exact oneEdge_free_fkMeasure_ne_wired_half hd.symm
  · have hfree := isGeometricFKLimit_eq_freeOneEdgeLimit hmem
    exact freeOneEdgeLimit_ne_wiredOneEdgeLimitHalf hfree.symm

end GeometricRepair

end FK.InfiniteVolume.Scope
