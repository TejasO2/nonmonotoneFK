import FK.SourceFamily
import FK.SourceBoundary
import FK.Theorem110Strassen
import FK.OrderedKernelNonpercolation

/-!
# Source-scope strong uniqueness from the nested boundary estimate

The input `HasNestedBoundaryBounds` is precisely the global consequence of the
finite Lemma 2.1 coupling estimate, with source outer-boundary classes and the
literal boundary event `∂Λ ↔ ∂Δ`.  It is not asserted here.  Given it
and one source FK weak limit, this file proves uniqueness of every source weak
limit and then of the full all-finite-region source FK family by Proposition
1.8(1) and the proved tail Choquet decomposition.  Neither Theorem 5.1 nor
Proposition 1.8(2) is used on this classical route.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology Classical

namespace FK.SourceUniqueness

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.RandomClosedBoundary
open FK.RandomRegionKernel
open FK.SourceRegions
open CurvatureVariance.Infra.Percolation

universe u

section Family

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- A genuine FK weak limit with source outer-boundary conditions along one
induced vertex exhaustion. -/
def IsSourceFKLimit (E : VertexExhaustion V)
    (μ : ProbabilityMeasure (Configuration G.edgeSet)) : Prop :=
  ∃ α : ∀ n, (E.box n).BoundaryPartition,
    Prop42Source.SourceBoundaryClasses (E.data (G := G)) α ∧
      IsFKLimit (E.exhaustion (G := G)) hq hp α μ

/-- The paper's weak-limit family `W_{p,q}`, with all induced vertex
exhaustions and all source outer-boundary schedules allowed. -/
def SourceWeakLimits : Set (ProbabilityMeasure (Configuration G.edgeSet)) :=
  {μ | ∃ E : VertexExhaustion V, IsSourceFKLimit hq hp E μ}

/-- The paper's total FK family: geometric conventions with DLR equations at
all finite vertex regions, together with all source weak limits. -/
def SourceFKMeasures : Set (ProbabilityMeasure (Configuration G.edgeSet)) :=
  (⋃ Φ : SourceConvention G hq hp,
    {μ | IsSourceGeometry Φ ∧ μ ∈ SourceDLRMeasures Φ}) ∪
    SourceWeakLimits (G := G) hq hp

lemma mem_sourceWeakLimits {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    {E : VertexExhaustion V} (hμ : IsSourceFKLimit hq hp E μ) :
    μ ∈ SourceWeakLimits (G := G) hq hp :=
  ⟨E, hμ⟩

lemma mem_sourceFKMeasures_of_weak {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceWeakLimits (G := G) hq hp) :
    μ ∈ SourceFKMeasures (G := G) hq hp :=
  Or.inr hμ

lemma mem_sourceFKMeasures_of_dlr {Φ : SourceConvention G hq hp}
    (hΦ : IsSourceGeometry Φ) {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceDLRMeasures Φ) :
    μ ∈ SourceFKMeasures (G := G) hq hp :=
  Or.inl (Set.mem_iUnion.mpr ⟨Φ, hΦ, hμ⟩)

/-- Proposition 1.8(1) inside the source family: an extremal all-region DLR
law is a weak limit with genuine source outer-boundary classes. -/
theorem isSourceFKLimit_of_extremal_dlr (E : VertexExhaustion V)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ)
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration G.edgeSet) =>
        (η : Measure (Configuration G.edgeSet))) '' SourceDLRMeasures Φ)
      (μ : Measure (Configuration G.edgeSet))) :
    IsSourceFKLimit hq hp E μ := by
  have hμr : μ ∈ DLRMeasures (E.exhaustion (G := G)) (assignment E Φ) hq hp :=
    (mem_sourceDLR_iff_mem_dlr_restrict E Φ μ).1 hμ
  have hset : DLRMeasures (E.exhaustion (G := G)) (assignment E Φ) hq hp =
      SourceDLRMeasures Φ := by
    ext ν
    exact (mem_sourceDLR_iff_mem_dlr_restrict E Φ ν).symm
  have hextR : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration G.edgeSet) =>
        (η : Measure (Configuration G.edgeSet))) ''
        DLRMeasures (E.exhaustion (G := G)) (assignment E Φ) hq hp)
      (μ : Measure (Configuration G.edgeSet)) := by
    rwa [hset]
  have hae := tendsto_ae_exteriorConditionalLaw_probabilityMeasure_of_extremal_dlr
    (E.exhaustion (G := G)) (assignment E Φ) hq hp μ hμr hextR
  obtain ⟨ω, hω⟩ := hae.exists
  let η : ∀ n, (E.box n).Exterior := fun n =>
    FKLimit.exteriorRestriction (E.box n).edges ω
  refine ⟨fun n => (assignment E Φ).partition n (η n),
    sourceBoundaryClasses_assignment E Φ hΦ η, ?_⟩
  exact (tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw
    (E.exhaustion (G := G)) hq hp (assignment E Φ).partition η μ).2 hω

/-- Nested equation-(9) estimate at source scope.  The right side is the mass
that the observation's finite root set connects to the inner region's
vertex boundary (`IsRegionBoundary`).
The bound is required only for source outer-boundary schedules. -/
def HasNestedBoundaryBounds (ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (roots : Finset G.edgeSet → Finset V) : Prop :=
  ∀ (D E : VertexExhaustion V)
    (α : ∀ n, (E.box n).BoundaryPartition)
    (β : ∀ n, (D.box n).BoundaryPartition),
    Prop42Source.SourceBoundaryClasses (E.data (G := G)) α →
    Prop42Source.SourceBoundaryClasses (D.data (G := G)) β →
    ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)),
      ∀ᶠ m in atTop, ∀ᶠ n in atTop,
        |(((E.box n).finiteVolumeLaw hq hp (α n)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S) -
          (((D.box m).finiteVolumeLaw hq hp (β m)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S)| ≤
        (ρ : Measure (Configuration G.edgeSet)).real
          (boundaryConnection G (roots I) (D.region m))

/-- The literal finite nested estimate delivered by Lemma 2.1: for every pair
of nested induced region boxes, with source boundary conditions and a cylinder
supported in the inner box, the two finite-volume masses differ by at most the
upper law's boundary-connection probability. -/
def NestedEquationNine (ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (roots : Finset G.edgeSet → Finset V) : Prop :=
  ∀ (D E : VertexExhaustion V)
    (α : ∀ n, (E.box n).BoundaryPartition)
    (β : ∀ n, (D.box n).BoundaryPartition),
    Prop42Source.SourceBoundaryClasses (E.data (G := G)) α →
    Prop42Source.SourceBoundaryClasses (D.data (G := G)) β →
    ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)) (m n : ℕ),
      I ⊆ (D.box m).edges →
        Nonempty (NestedMixture.NestedBox (D.box (G := G) m) (E.box (G := G) n)) →
      |(((E.box n).finiteVolumeLaw hq hp (α n)) :
          Measure (Configuration G.edgeSet)).real (cylinder I S) -
        (((D.box m).finiteVolumeLaw hq hp (β m)) :
          Measure (Configuration G.edgeSet)).real (cylinder I S)| ≤
      (ρ : Measure (Configuration G.edgeSet)).real
        (boundaryConnection G (roots I) (D.region m))

/-- The source proof's choices `m`, then `n_m`, turn the literal nested
finite estimate into the eventual estimate used by the limit theorem. -/
theorem hasNestedBoundaryBounds_of_equationNine
    {ρ : ProbabilityMeasure (Configuration G.edgeSet)}
    {roots : Finset G.edgeSet → Finset V}
    (h : NestedEquationNine (G := G) hq hp ρ roots) :
    HasNestedBoundaryBounds (G := G) hq hp ρ roots := by
  intro D E α β hα hβ I S
  filter_upwards [(D.exhaustion (G := G)).eventually_subset I] with m hm
  filter_upwards [E.eventually_nest (G := G) D m] with n hn
  exact h D E α β hα hβ I S m n hm hn

end Family

/-! ## Compactness supplies a source weak limit -/

section Existence

variable {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- By compactness, a subsequence of the free finite-volume laws converges.
The subsequence is again an induced vertex exhaustion, so the limit belongs to
the source weak-limit family, with no arbitrary-box enlargement. -/
theorem sourceWeakLimits_nonempty :
    (SourceWeakLimits (G := G) hq hp).Nonempty := by
  classical
  let E : VertexExhaustion V :=
    Classical.choice (VertexExhaustion.exists_vertexExhaustion (V := V))
  let α : ∀ n, (E.box (G := G) n).BoundaryPartition :=
    fun n => (E.box (G := G) n).graph.freeBoundary
  obtain ⟨μ, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq
    (fun n => (E.box (G := G) n).finiteVolumeLaw hq hp (α n))
  let D : VertexExhaustion V := {
    region := fun n => E.region (φ n)
    monotone := E.monotone.comp hφ.monotone
    covers := by
      intro v
      obtain ⟨N, hN⟩ := E.covers v
      obtain ⟨n, hn⟩ := (hφ.tendsto_atTop.eventually (eventually_ge_atTop N)).exists
      exact ⟨n, E.monotone hn hN⟩ }
  have hsrc : Prop42Source.SourceBoundaryClasses (D.data (G := G))
      (fun n => (D.box (G := G) n).graph.freeBoundary) := by
    intro n c _hc
    exact (D.box (G := G) n).graph.hasSingletonBoundaryClass_free c
  refine ⟨μ, D, fun n => (D.box (G := G) n).graph.freeBoundary, hsrc, ?_⟩
  simpa only [IsFKLimit, Function.comp_def, D, α, VertexExhaustion.box,
    VertexExhaustion.exhaustion, VertexExhaustion.growingFamily,
    NestedMixture.GrowingFamily.exh] using hμ

end Existence

section Choquet

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- If all source weak limits equal `μ₀`, every geometric all-region DLR law
also equals `μ₀`.  This is the source-simplex step of Proposition 1.8(1). -/
theorem eq_sourceDLR_of_unique_sourceWeakLimits (E : VertexExhaustion V)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ₀ : ProbabilityMeasure (Configuration G.edgeSet))
    (hW : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceWeakLimits (G := G) hq hp → μ = μ₀)
    (ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hν : ν ∈ SourceDLRMeasures Φ) : ν = μ₀ := by
  apply eq_dlr_of_extremal_unique (E.exhaustion (G := G)) (assignment E Φ)
    hq hp ν μ₀ ((mem_sourceDLR_iff_mem_dlr_restrict E Φ ν).1 hν)
  intro ξ hξ
  obtain ⟨η, hη, hcoe⟩ := hξ.1
  have hηsource : η ∈ SourceDLRMeasures Φ :=
    (mem_sourceDLR_iff_mem_dlr_restrict E Φ η).2 hη
  have hξsource : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration G.edgeSet) =>
        (η : Measure (Configuration G.edgeSet))) '' SourceDLRMeasures Φ)
      (ξ : Measure (Configuration G.edgeSet)) := by
    have hset : DLRMeasures (E.exhaustion (G := G)) (assignment E Φ) hq hp =
        SourceDLRMeasures Φ := by
      ext ν'
      exact (mem_sourceDLR_iff_mem_dlr_restrict E Φ ν').symm
    rwa [← hset]
  have hξ' : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration G.edgeSet) =>
        (η : Measure (Configuration G.edgeSet))) '' SourceDLRMeasures Φ)
      (η : Measure (Configuration G.edgeSet)) := by
    have hcast : (η : Measure (Configuration G.edgeSet)) =
        (ξ : Measure (Configuration G.edgeSet)) := hcoe
    rw [hcast]
    exact hξsource
  have hlim : IsSourceFKLimit hq hp E η :=
    isSourceFKLimit_of_extremal_dlr hq hp E Φ hΦ η hηsource hξ'
  have hημ : η = μ₀ := hW η (mem_sourceWeakLimits hq hp hlim)
  have hval : (η : Measure (Configuration G.edgeSet)) =
      (μ₀ : Measure (Configuration G.edgeSet)) := congrArg
    (fun x : ProbabilityMeasure (Configuration G.edgeSet) =>
      (x : Measure (Configuration G.edgeSet))) hημ
  exact Subtype.ext (hcoe.symm.trans hval)

end Choquet

section Main

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- **Strong uniqueness modulo the general finite nested coupling estimate.**
One nonpercolating upper law controls the nested boundary errors.  The two remaining
inputs are exactly a source weak limit (existence) and `HasNestedBoundaryBounds`
(the global consequence of Lemma 2.1).  No metric exhaustion, Theorem 5.1,
Proposition 1.8(2), fixed convention, or all-measurable-setoid-class argument
is hidden in the statement. -/
theorem existsUnique_sourceFKMeasures_of_nested_boundaryBounds
    (ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V)
    (hbound : HasNestedBoundaryBounds (G := G) hq hp ρ roots)
    (hne : (SourceWeakLimits (G := G) hq hp).Nonempty) :
    ∃! μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceFKMeasures (G := G) hq hp := by
  obtain ⟨μ₀, hμ₀⟩ := hne
  obtain ⟨D₀, hD₀⟩ := hμ₀
  have hW : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceWeakLimits (G := G) hq hp → μ = μ₀ := by
    intro μ hμ
    obtain ⟨E, α, hα, hlim⟩ := hμ
    obtain ⟨β, hβ, hlim₀⟩ := hD₀
    exact eq_of_isFKLimit_of_nested_boundary_bounds D₀ E hq hp α β μ μ₀ ρ
      hlim hlim₀ hρ roots (hbound D₀ E α β hα hβ)
  refine ⟨μ₀, mem_sourceFKMeasures_of_weak hq hp ⟨D₀, hD₀⟩, ?_⟩
  intro ν hν
  rcases hν with hν | hν
  · obtain ⟨Φ, hΦ, hν⟩ := Set.mem_iUnion.mp hν
    exact eq_sourceDLR_of_unique_sourceWeakLimits hq hp D₀ Φ hΦ μ₀ hW ν hν
  · exact hW ν hν

end Main

section Window

variable {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- **Theorem 1.10 modulo its two actual probabilistic/geometric inputs.**
`hdom` is the nonpercolating stochastic-dominant conclusion supplied by the
AG/Theorem 1.4 window, and `hEq9` is the literal finite nested estimate
supplied by Lemma 2.1.  Existence of a source weak limit is proved above by
compactness, and the source choices `m`, then `n_m`, are proved above.
The conclusion is strong uniqueness of the source FK family and almost-sure
nonpercolation of its unique law. -/
theorem theorem_1_10_modulo_AG_window_and_lemma_2_1
    (ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V)
    (hEq9 : NestedEquationNine (G := G) hq hp ρ roots)
    (hdom : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceWeakLimits (G := G) hq hp → FKLimit.StochasticallyDominates ρ μ) :
    ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp = {μ₀} ∧
        ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  have hne := sourceWeakLimits_nonempty (G := G) hq hp
  obtain ⟨w, hw⟩ := hne
  obtain ⟨μ₀, hμ₀, huniq⟩ := existsUnique_sourceFKMeasures_of_nested_boundaryBounds
    hq hp ρ hρ roots (hasNestedBoundaryBounds_of_equationNine hq hp hEq9) ⟨w, hw⟩
  have hset : SourceFKMeasures (G := G) hq hp = {μ₀} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hμ₀, huniq⟩
  have hw₀ : w = μ₀ := huniq w (mem_sourceFKMeasures_of_weak hq hp hw)
  have hnon : ∀ᵐ ω ∂(w : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    FKLimit.ae_nonPercolating_of_stochasticallyDominates G (hdom w hw) hρ
  refine ⟨μ₀, hset, ?_⟩
  rwa [← hw₀]

end Window

end FK.SourceUniqueness
