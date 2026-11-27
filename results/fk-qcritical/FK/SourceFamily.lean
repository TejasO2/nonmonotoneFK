import FK.SourceEscape
import FK.Theorem110Assembly
import FK.Proposition42Source
import FK.CoherentAllBoxes

/-!
# The source FK family and weak-limit representation of extremal laws

The finite regions here are the actual `boxOf s` boxes from `SourceRegions`.
We identify their exterior-walk geometry with the `SimpleGraphBoxData`
geometry, prove that geometric source conventions assign partitions of the
source outer boundary, and apply the proved reverse-martingale/Choquet layer.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology Classical

namespace FK.SourceUniqueness

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.RandomClosedBoundary
open FK.RandomRegionKernel
open FK.SourceRegions
open CurvatureVariance.Infra.Percolation

universe u

section Geometry

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- On an edge outside a region box, the two closed-interior configurations
are literally the same. -/
lemma extendExterior_eq_closeInside_of_notMem (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) (e : G.edgeSet)
    (he : e ∉ (boxOf (G := G) s).edges) :
    extendExterior (G := G) (s : Set V) s.finite_toSet η e =
      closeInside (boxOf (G := G) s) η e := by
  simp [extendExterior, closeInside, FiniteBox.glue, he]

/-- A noninterior edge cannot belong to the induced interior box. -/
lemma not_mem_box_of_mem_nonInterior (s : Finset V) {e : G.edgeSet}
    (he : (e : Sym2 V) ∈ nonInteriorEdges (s : Set V)) :
    e ∉ (boxOf (G := G) s).edges := by
  intro hbox
  have hint := mem_interiorEdgeSet_of_mem_box (G := G) (s : Set V)
    s.finite_toSet hbox
  obtain ⟨x, hx, hxs⟩ := he
  exact hxs (hint x hx)

/-- An open close-interior edge is noninterior to the region. -/
lemma mem_nonInterior_of_closeInside_open (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) {e : G.edgeSet}
    (he : closeInside (boxOf (G := G) s) η e = true) :
    (e : Sym2 V) ∈ nonInteriorEdges (s : Set V) := by
  by_contra hn
  have hall : ∀ x ∈ (e : Sym2 V), x ∈ (s : Set V) := by
    intro x hx
    by_contra hxs
    exact hn ⟨x, hx, hxs⟩
  have hbox : e ∈ (boxOf (G := G) s).edges :=
    (finite_interiorEdgeSet (G := G) s.finite_toSet).mem_toFinset.mpr hall
  have hclosed : closeInside (boxOf (G := G) s) η e = false := by
    simp [closeInside, FiniteBox.glue, hbox]
  rw [hclosed] at he
  contradiction

/-- Transport an exterior open walk to the closed-interior configuration. -/
lemma isOpenIn_closeInside_of_extendExterior (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) {a b : V} (p : G.Walk a b)
    (hp : IsOpenIn (extendExterior (G := G) (s : Set V) s.finite_toSet η)
      (nonInteriorEdges (s : Set V)) p) :
    IsOpenIn (closeInside (boxOf (G := G) s) η) Set.univ p := by
  induction p with
  | nil => exact isOpenIn_nil
  | @cons a b c hab q ih =>
      rw [isOpenIn_cons] at hp ⊢
      refine ⟨⟨Set.mem_univ _, ?_⟩, ih hp.2⟩
      let e : G.edgeSet := ⟨s(a, b), hab⟩
      have hbox : e ∉ (boxOf (G := G) s).edges :=
        not_mem_box_of_mem_nonInterior s hp.1.1
      change closeInside (boxOf (G := G) s) η e = true
      rw [← extendExterior_eq_closeInside_of_notMem s η e hbox]
      exact hp.1.2

/-- Conversely, every open walk in the closed-interior configuration avoids
all induced interior edges and hence is an exterior open walk. -/
lemma isOpenIn_extendExterior_of_closeInside (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) {a b : V} (p : G.Walk a b)
    (hp : IsOpenIn (closeInside (boxOf (G := G) s) η) Set.univ p) :
    IsOpenIn (extendExterior (G := G) (s : Set V) s.finite_toSet η)
      (nonInteriorEdges (s : Set V)) p := by
  induction p with
  | nil => exact isOpenIn_nil
  | @cons a b c hab q ih =>
      rw [isOpenIn_cons] at hp ⊢
      let e : G.edgeSet := ⟨s(a, b), hab⟩
      have hopen : closeInside (boxOf (G := G) s) η e = true := hp.1.2
      have hn := mem_nonInterior_of_closeInside_open s η hopen
      have hbox : e ∉ (boxOf (G := G) s).edges :=
        not_mem_box_of_mem_nonInterior s hn
      refine ⟨⟨hn, ?_⟩, ih hp.2⟩
      change extendExterior (G := G) (s : Set V) s.finite_toSet η e = true
      rw [extendExterior_eq_closeInside_of_notMem s η e hbox]
      exact hopen

/-- The two exterior-walk descriptions have exactly the same connection
relation. -/
theorem openConnected_extendExterior_iff_closeInside (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) (x y : V) :
    OpenConnected G (extendExterior (G := G) (s : Set V) s.finite_toSet η)
        (nonInteriorEdges (s : Set V)) x y ↔
      OpenConnected G (closeInside (boxOf (G := G) s) η) Set.univ x y := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, isOpenIn_closeInside_of_extendExterior s η p hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, isOpenIn_extendExterior_of_closeInside s η p hp⟩

/-- The `SourceRegions` component setoid is the ordinary finite-box exterior
component setoid. -/
theorem sourceComponents_eq_data_components (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) :
    sourceComponents (G := G) s η =
      openPathSetoid G (closeInside (boxOf (G := G) s) η) Set.univ
        (fun x : (boxOf (G := G) s).Vertex => x.1) := by
  apply Setoid.ext
  intro x y
  exact openConnected_extendExterior_iff_closeInside s η x.1 y.1

/-- Infinitude of the corresponding exterior cluster is likewise identical. -/
theorem sourceInfinite_eq_data_infinite (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) (x : (boxOf (G := G) s).Vertex) :
    sourceInfinite (G := G) s η x ↔
      ExteriorInfiniteCluster G (closeInside (boxOf (G := G) s) η)
        Set.univ x.1 := by
  unfold sourceInfinite ExteriorInfiniteCluster
  have hset : {y | OpenConnected G
      (extendExterior (G := G) (s : Set V) s.finite_toSet η)
      (nonInteriorEdges (s : Set V)) x.1 y} =
    {y | OpenConnected G (closeInside (boxOf (G := G) s) η) Set.univ x.1 y} := by
    ext y
    exact openConnected_extendExterior_iff_closeInside s η x.1 y
  rw [hset]

end Geometry

/-! ## Restricting an all-region source convention to an exhaustion -/

section Restriction

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}

/-- Restriction of an all-finite-region source convention to a vertex
exhaustion. -/
noncomputable def assignment (E : VertexExhaustion V)
    (Φ : SourceConvention G hq hp) : BoundaryAssignment (E.exhaustion (G := G)).box where
  partition n := Φ.partition (E.region n)
  measurable_partition n := Φ.measurable_partition (E.region n)

/-- Source DLR equations restrict to the usual DLR class on every vertex
exhaustion. -/
lemma mem_dlr_restrict {E : VertexExhaustion V} {Φ : SourceConvention G hq hp}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceDLRMeasures Φ) :
    μ ∈ DLRMeasures (E.exhaustion (G := G)) (assignment E Φ) hq hp := by
  intro n
  exact hμ (E.region n)

/-- A coherent source specification can be tested on any one cofinal vertex
exhaustion.  No extremality is lost by restricting the DLR class. -/
theorem mem_sourceDLR_iff_mem_dlr_restrict (E : VertexExhaustion V)
    (Φ : SourceConvention G hq hp) (μ : ProbabilityMeasure (Configuration G.edgeSet)) :
    μ ∈ SourceDLRMeasures Φ ↔
      μ ∈ DLRMeasures (E.exhaustion (G := G)) (assignment E Φ) hq hp := by
  constructor
  · exact mem_dlr_restrict
  · intro hμ s
    obtain ⟨n, hn⟩ := E.exists_subset s
    exact CoherentAllBoxes.isDLR_of_isDLR_of_compatible
      (boxOf (G := G) s) (E.box n) hq hp
      (Φ.partition s) (Φ.measurable_partition s)
      ((assignment E Φ).partition n) ((assignment E Φ).measurable_partition n) μ
      (hμ n) (Φ.compatible hn)

/-- The two source geometry descriptions agree on every exhaustion. -/
theorem isGeometric_assignment (E : VertexExhaustion V)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ) :
    IsGeometric (E.data (G := G)).geometry (assignment E Φ) := by
  constructor
  · intro n η
    have h := hΦ.1 (E.region n) η
    rw [sourceComponents_eq_data_components (G := G) (E.region n) η] at h
    exact h
  · intro n η
    have h : SeparatesFiniteComponents (sourceComponents (G := G) (E.region n) η)
        (Φ.partition (E.region n) η) (sourceInfinite (G := G) (E.region n) η) :=
      hΦ.2 (E.region n) η
    rw [sourceComponents_eq_data_components (G := G) (E.region n) η] at h
    have hi : sourceInfinite (G := G) (E.region n) η =
        (E.data (G := G)).geometry.infinite n η := by
      funext x
      exact propext (sourceInfinite_eq_data_infinite (E.region n) η x)
    rw [hi] at h
    intro x y hxy hfin
    exact h hxy hfin

/-- Geometric source conventions assign source outer-boundary classes after
evaluation at every exterior configuration. -/
theorem sourceBoundaryClasses_assignment (E : VertexExhaustion V)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (η : ∀ n, (E.box n).Exterior) :
    Prop42Source.SourceBoundaryClasses (E.data (G := G))
      (fun n => (assignment E Φ).partition n (η n)) := by
  intro n
  exact (Prop42Source.sourceConvention_of_isGeometric (E.data (G := G))
    (isGeometric_assignment E Φ hΦ) (E.data_vertex_injective (G := G))) n (η n)

end Restriction

end FK.SourceUniqueness
