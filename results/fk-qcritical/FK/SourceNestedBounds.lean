import FK.SourceGlobalWindow
import FK.SourceUniqueness

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.Adaptive.NestedSumGeometry

open FK.Finite FK.Finite.LabelledMultigraph FK.Exploration.FKCoupling
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.SourceUniqueness
open FK.Prop42Source

universe uV

/-- Empty observations give a zero estimate and require no exploration seed. -/
lemma empty_base_abs_sub_le_boundary {V : Type uV} {G : SimpleGraph V}
    (μ ν ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (R : Finset V) (S : Set ((∅ : Finset G.edgeSet) → Bool)) :
    |(μ : Measure (Configuration G.edgeSet)).real (cylinder ∅ S) -
      (ν : Measure (Configuration G.edgeSet)).real (cylinder ∅ S)| ≤
    (ρ : Measure (Configuration G.edgeSet)).real
      (boundaryConnection G (edgeRoots G ∅) R) := by
  let z : (∅ : Finset G.edgeSet) → Bool := fun _ => false
  have hrestrict (ω : Configuration G.edgeSet) : (∅ : Finset G.edgeSet).restrict ω = z :=
    Subsingleton.elim _ _
  have hcyl : cylinder (α := fun _ : G.edgeSet => Bool) (∅ : Finset G.edgeSet) S =
      if z ∈ S then Set.univ else ∅ := by
    ext ω
    by_cases hz : z ∈ S <;> simp [cylinder, hz, hrestrict]
  have hb : boundaryConnection G (edgeRoots G ∅) R = ∅ := by
    ext ω
    simp [boundaryConnection, NestedAssembly.connectsFinsetTo, edgeRoots]
  rw [hb]
  by_cases hz : z ∈ S <;> simp [hcyl, hz]

/-- Canonical ordinary nested coupling gives the eventual source boundary
bounds used by the uniqueness theorem, on every vertex exhaustion. -/
theorem canonicalSource_hasNestedBoundaryBounds {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    HasNestedBoundaryBounds (G := G) hq hp₁.le
      (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le) (edgeRoots G) := by
  intro D E α β hα hβ K S
  by_cases hK : K = ∅
  · subst K
    filter_upwards [] with m
    filter_upwards [] with n
    exact empty_base_abs_sub_le_boundary
      ((E.box (G := G) n).finiteVolumeLaw hq hp₁.le (α n))
      ((D.box (G := G) m).finiteVolumeLaw hq hp₁.le (β m))
      (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le)
      (D.region m) S
  · have hK0 : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hK
    filter_upwards [(D.exhaustion (G := G)).eventually_subset K] with m hm
    filter_upwards [E.eventually_subset (D.region m)] with n hn
    let e : (D.box (G := G) m).edges := ⟨hK0.choose, hm hK0.choose_spec⟩
    let e₀ : ((D.box (G := G) m).indexedGraph (edgeIndex _)).Edge ⊕
        (outsideGraph (E.box (G := G) n) (D.box (G := G) m)).Edge :=
      Sum.inl ((edgeIndex (D.box (G := G) m)).symm e)
    exact canonicalSource_abs_sub_le_boundary D E m n hn (α n) (β m) (hα n) (hβ m)
      (outsideGraph (E.box (G := G) n) (D.box (G := G) m)).freeBoundary
      hq hp₀ hp₁ e₀ K S hm

/-- Strong source uniqueness from the proved ordinary nested coupling and
nonpercolation of the corresponding global upper Bernoulli law. -/
theorem canonicalSource_existsUnique_sourceFKMeasures {V : Type uV}
    [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hρ : ∀ᵐ ω ∂(globalBernoulli G.edgeSet
      (upperRateNN_lt_one hq hp₀ hp₁).le : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    ∃! μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceFKMeasures (G := G) hq hp₁.le := by
  obtain ⟨w, hw⟩ := sourceWeakLimits_nonempty (G := G) hq hp₁.le
  exact existsUnique_sourceFKMeasures_of_nested_boundaryBounds hq hp₁.le
    (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le)
    hρ (edgeRoots G) (canonicalSource_hasNestedBoundaryBounds hq hp₀ hp₁) ⟨w, hw⟩

end FK.Adaptive.NestedSumGeometry
