import FK.NestedArmUniqueness
import FK.SourceRegions
import FK.NestedMixture.NestedBox
import FK.NestedMixture.Limit

/-!
# Arbitrary vertex exhaustions and nonpercolating escape limits

This module isolates the arbitrary-exhaustion limit in the classical proof of
Theorem 1.9.  It does not prove the finite exploration identity in Lemma 2.1.
It proves instead that the event that a fixed finite set of roots connects to
the complement of a growing finite vertex region has probability tending to zero
under every nonpercolating law.  Thus metric balls are not needed for the final
`n → ∞`, then `m → ∞`, passage.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology Classical

namespace FK.SourceUniqueness

open FK.InfiniteVolume
open FK.InfiniteVolume.NestedAssembly
open FK.RandomClosedBoundary
open FK.RandomRegionKernel
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

/-- A genuine increasing, cofinal sequence of finite vertex regions. -/
structure VertexExhaustion (V : Type u) where
  region : ℕ → Finset V
  monotone : Monotone region
  covers : ∀ v : V, ∃ n, v ∈ region n

namespace VertexExhaustion

variable {V : Type u} (E : VertexExhaustion V)

lemma eventually_mem (v : V) : ∀ᶠ n in atTop, v ∈ E.region n := by
  obtain ⟨N, hN⟩ := E.covers v
  filter_upwards [eventually_ge_atTop N] with n hn
  exact E.monotone hn hN

lemma eventually_subset (K : Finset V) : ∀ᶠ n in atTop, K ⊆ E.region n := by
  change ∀ᶠ n in atTop, ∀ v ∈ K, v ∈ E.region n
  rw [Finset.eventually_all]
  exact fun v _ => E.eventually_mem v

lemma exists_subset (K : Finset V) : ∃ n, K ⊆ E.region n :=
  (E.eventually_subset K).exists

/-- The induced labelled finite boxes of a vertex exhaustion. -/
noncomputable def box {G : SimpleGraph V} [G.LocallyFinite] (n : ℕ) :
    FiniteBox G.edgeSet :=
  boxOf (G := G) (E.region n)

lemma mem_box_edges_iff {G : SimpleGraph V} [G.LocallyFinite] (n : ℕ)
    (e : G.edgeSet) :
    e ∈ (E.box n).edges ↔ e ∈ interiorEdgeSet G ((E.region n : Finset V) : Set V) := by
  exact (finite_interiorEdgeSet (G := G) (E.region n).finite_toSet).mem_toFinset

/-- The canonical global embedding of the induced region boxes. -/
noncomputable def data {G : SimpleGraph V} [G.LocallyFinite] :
    ConventionTransport.SimpleGraphBoxData G E.box where
  vertex _ x := x.1
  endpoint _ e := edgeFst_edgeSnd_eq (G := G) (e : G.edgeSet)

lemma data_vertex_injective {G : SimpleGraph V} [G.LocallyFinite] (n : ℕ) :
    Function.Injective ((E.data (G := G)).vertex n) := by
  intro x y h
  exact Subtype.ext h

/-- Nesting of induced boxes for an arbitrary inclusion of vertex regions. -/
noncomputable def nest {G : SimpleGraph V} [G.LocallyFinite]
    (D : VertexExhaustion V) (m n : ℕ) (h : D.region m ⊆ E.region n) :
    NestedBox (D.box (G := G) m) (E.box (G := G) n) where
  edge_sub := by
    intro e he
    rw [D.mem_box_edges_iff] at he
    rw [E.mem_box_edges_iff]
    exact interiorEdgeSet_mono (fun _ hx => h hx) he
  vert := fun x => ⟨x.1, h x.2⟩
  vert_inj := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : (E.box n).Vertex => z.1) hxy)
  src := by
    intro e
    apply Subtype.ext
    rfl
  tgt := by
    intro e
    apply Subtype.ext
    rfl

/-- Every fixed stage of one vertex exhaustion embeds eventually in every
other vertex exhaustion.  This is the source proof's selection of `n_m`. -/
theorem eventually_nest {G : SimpleGraph V} [G.LocallyFinite]
    (D : VertexExhaustion V) (m : ℕ) :
    ∀ᶠ n in atTop, Nonempty (NestedBox (D.box (G := G) m) (E.box (G := G) n)) := by
  filter_upwards [E.eventually_subset (D.region m)] with n hn
  exact ⟨E.nest D m n hn⟩

/-- One vertex exhaustion together with all its induced nestings. -/
noncomputable def growingFamily {G : SimpleGraph V} [G.LocallyFinite] :
    GrowingFamily G.edgeSet where
  box := E.box
  edges_mono := by
    intro m n hmn e he
    rw [E.mem_box_edges_iff] at he ⊢
    exact interiorEdgeSet_mono (fun _ hx => E.monotone hmn hx) he
  covers := by
    intro e
    let K : Finset V := {edgeFst e, edgeSnd e}
    obtain ⟨n, hn⟩ := E.exists_subset K
    refine ⟨n, (E.mem_box_edges_iff n e).2 ?_⟩
    intro x hx
    rw [← edgeFst_edgeSnd_eq e] at hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact hn (by simp [K])
    · exact hn (by simp [K])
  nest := by
    intro m n hmn
    exact E.nest E m n (E.monotone hmn)

/-- The underlying edge exhaustion of the induced finite boxes. -/
noncomputable def exhaustion {G : SimpleGraph V} [G.LocallyFinite] :
    BoxExhaustion G.edgeSet :=
  E.growingFamily.exh

/-- Finite initial segments of a surjective enumeration form a vertex
exhaustion. -/
noncomputable def ofSurjective (f : ℕ → V) (hf : Function.Surjective f) :
    VertexExhaustion V where
  region n := (Finset.range (n + 1)).image f
  monotone := by
    intro m n hmn
    exact Finset.image_mono f (Finset.range_mono (Nat.add_le_add_right hmn 1))
  covers := by
    intro v
    obtain ⟨n, rfl⟩ := hf v
    refine ⟨n, Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩⟩

/-- Every nonempty countable vertex type has a canonical source exhaustion. -/
theorem exists_vertexExhaustion [Countable V] [Nonempty V] :
    Nonempty (VertexExhaustion V) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat V
  exact ⟨ofSurjective f hf⟩

end VertexExhaustion

/-! ## Escape from a finite root set out of a vertex region -/

section Escape

variable {V : Type u}

/-- Some root in `roots` is openly connected to a vertex outside `R`. -/
def escape (G : SimpleGraph V) (roots : Finset V) (R : Finset V) : Set (G.edgeSet → Bool) :=
  connectsFinsetTo G roots {w | w ∉ R}

lemma measurableSet_escape [Countable V] (roots R : Finset V) :
    MeasurableSet (escape G roots R) := by
  exact measurableSet_connectsFinsetTo roots _

lemma escape_antitone {roots : Finset V} {R : ℕ → Finset V} (hR : Monotone R) :
    Antitone (fun n => escape G roots (R n)) := by
  intro m n hmn ω hω
  rcases hω with ⟨a, ha, w, hw, haw⟩
  exact ⟨a, ha, w, fun hwR => hw (hR hmn hwR), haw⟩

/-- A configuration in every escape event has an infinite open cluster at one
of the finitely many roots.  The proof uses only finiteness of the union of the
root clusters and cofinality of the vertex exhaustion. -/
theorem mem_iInter_escape_imp_exists_infinite (roots : Finset V)
    (E : VertexExhaustion V) {ω : G.edgeSet → Bool}
    (hω : ω ∈ ⋂ n, escape G roots (E.region n)) :
    ∃ a ∈ roots, {w | OpenConnected G ω Set.univ a w}.Infinite := by
  classical
  by_contra hno
  push_neg at hno
  let K : Finset V := roots.biUnion fun a =>
    if ha : {w | OpenConnected G ω Set.univ a w}.Finite then ha.toFinset else ∅
  have hK : ∀ a ∈ roots, ∀ w, OpenConnected G ω Set.univ a w → w ∈ K := by
    intro a ha w haw
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    have hfin : {w | OpenConnected G ω Set.univ a w}.Finite := hno a ha
    simp only [hfin, dite_true]
    exact hfin.mem_toFinset.mpr haw
  obtain ⟨n, hn⟩ := E.exists_subset K
  have hmem := Set.mem_iInter.mp hω n
  rcases hmem with ⟨a, ha, w, hw, haw⟩
  exact hw (hn (hK a ha w haw))

/-- Under nonpercolation the nested escape events have null intersection. -/
lemma measure_iInter_escape_eq_zero [Countable V]
    (μ : Measure (G.edgeSet → Bool)) (roots : Finset V) (E : VertexExhaustion V)
    (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    μ (⋂ n, escape G roots (E.region n)) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hμ] with ω hω hmem
  obtain ⟨a, ha, hinf⟩ := mem_iInter_escape_imp_exists_infinite (G := G) roots E hmem
  exact hinf (hω a)

/-- **Arbitrary-exhaustion escape probabilities vanish.**  No metric-ball or
root-independent criticality hypothesis is used: nonpercolation itself makes
the decreasing intersection null. -/
theorem tendsto_measureReal_escape [Countable V]
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ]
    (roots : Finset V) (E : VertexExhaustion V)
    (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    Tendsto (fun n => μ.real (escape G roots (E.region n))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => μ (escape G roots (E.region n))) atTop
      (𝓝 (μ (⋂ n, escape G roots (E.region n)))) := by
    simpa only [Function.comp_def] using
      (tendsto_measure_iInter_atTop (μ := μ)
        (fun n => (measurableSet_escape (G := G) roots (E.region n)).nullMeasurableSet)
        (escape_antitone (G := G) E.monotone) ⟨0, measure_ne_top _ _⟩)
  rw [measure_iInter_escape_eq_zero μ roots E hμ] at hlim
  have hreal := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hlim
  simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using hreal

end Escape

/-! ## The arbitrary two-exhaustion limit -/

section Limit

variable {V : Type u} {G : SimpleGraph V}

/-- Cylinder comparison with an escape error identifies two weakly convergent
sequences.  This is exactly the source order of limits: outer index `n` first,
then the inner region index `m`. -/
theorem probabilityMeasure_eq_of_nested_escape_bounds [Countable V]
    (μs νs : ℕ → ProbabilityMeasure (G.edgeSet → Bool))
    (μ ν ρ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (G.edgeSet → Bool)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V) (D : VertexExhaustion V)
    (hbound : ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)) (m : ℕ),
      ∀ᶠ n in atTop,
        |(μs n : Measure (G.edgeSet → Bool)).real (cylinder I S) -
          (νs m : Measure (G.edgeSet → Bool)).real (cylinder I S)| ≤
        (ρ : Measure (G.edgeSet → Bool)).real (escape G (roots I) (D.region m))) :
    μ = ν := by
  apply Subtype.ext
  apply FKModel.measure_ext_of_eq_on_boolCylinders
    (μ : Measure (G.edgeSet → Bool)) (ν : Measure (G.edgeSet → Bool))
  intro I S
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  apply FKModel.eq_of_tendsto_of_eventually_abs_sub_le
    ((tendsto_probabilityMeasure_iff_cylinder_real_tendsto μs μ).mp hμ I S)
    ((tendsto_probabilityMeasure_iff_cylinder_real_tendsto νs ν).mp hν I S)
    (tendsto_measureReal_escape (ρ : Measure (G.edgeSet → Bool)) (roots I) D hρ)
  exact hbound I S

/-- Two actual FK weak limits along arbitrary induced vertex exhaustions agree
whenever equation (9) bounds every nested cylinder difference by the escape
probability of the inner region. -/
theorem eq_of_isFKLimit_of_nested_escape_bounds [Countable V] [G.LocallyFinite]
    (D E : VertexExhaustion V) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (E.box n).BoundaryPartition)
    (β : ∀ n, (D.box n).BoundaryPartition)
    (μ ν ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : IsFKLimit E.exhaustion hq hp α μ)
    (hν : IsFKLimit D.exhaustion hq hp β ν)
    (hρ : ∀ᵐ ω ∂(ρ : Measure (G.edgeSet → Bool)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V)
    (hbound : ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)) (m : ℕ),
      ∀ᶠ n in atTop,
        |(((E.box n).finiteVolumeLaw hq hp (α n)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S) -
          (((D.box m).finiteVolumeLaw hq hp (β m)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S)| ≤
        (ρ : Measure (Configuration G.edgeSet)).real (escape G (roots I) (D.region m))) :
    μ = ν := by
  exact probabilityMeasure_eq_of_nested_escape_bounds
    (fun n => (E.box n).finiteVolumeLaw hq hp (α n))
    (fun m => (D.box m).finiteVolumeLaw hq hp (β m)) μ ν ρ hμ hν hρ roots D hbound

end Limit

end FK.SourceUniqueness
