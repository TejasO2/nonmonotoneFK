import FK.FiniteGraphTransport

/-!
# Free-boundary FK invariance under vertex/edge transport, pointwise

`FK.FiniteGraphTransport` proves `PMF.map (transportConfig eV eE) (fkPMF free) =
fkPMF free`.  For the nested-box comparison we need the *pointwise* form
`φ_G(transportConfig ω) = φ_{G.transport}(ω)` together with invariance of the
partition function, and the resulting statement that masses of transported sets
agree.  No measurability is used.
-/

open scoped Classical BigOperators ENNReal NNReal
open FK.Finite

namespace FK.NestedMixture

open FK.Finite.LabelledMultigraph

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Two finite labelled multigraphs on the same vertex and edge types with the
same endpoint maps have the same FK PMF. -/
theorem fkPMF_eq_of_source_target_eq (s₁ t₁ s₂ t₂ : E → V) (hs : s₁ = s₂) (ht : t₁ = t₂)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : Setoid V) (ω : E → Bool) :
    ({ Vertex := V, Edge := E, source := s₁, target := t₁ } : LabelledMultigraph).fkPMF
        hq hp ξ ω
      = ({ Vertex := V, Edge := E, source := s₂, target := t₂ } : LabelledMultigraph).fkPMF
        hq hp ξ ω := by
  cases hs
  cases ht
  rfl

/-- Two finite labelled multigraphs on the same vertex and edge types with the
same endpoint maps have the same FK measure. -/
theorem fkMeasure_eq_of_source_target_eq (s₁ t₁ s₂ t₂ : E → V) (hs : s₁ = s₂)
    (ht : t₁ = t₂) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : Setoid V)
    (A : Set (E → Bool)) :
    ({ Vertex := V, Edge := E, source := s₁, target := t₁ } : LabelledMultigraph).fkMeasure
        hq hp ξ A
      = ({ Vertex := V, Edge := E, source := s₂, target := t₂ } : LabelledMultigraph).fkMeasure
        hq hp ξ A := by
  cases hs
  cases ht
  rfl

section Transport

variable (G : LabelledMultigraph) (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)

/-- The partition function of the free FK measure is invariant under transport. -/
theorem partitionFunction_free_transport (q p : NNReal) :
    G.partitionFunction q p G.freeBoundary =
      (G.transport eV eE).partitionFunction q p (G.transport eV eE).freeBoundary := by
  classical
  unfold LabelledMultigraph.partitionFunction
  rw [← Equiv.sum_comp (G.transportConfig eV eE)
    (fun ω => G.fkWeight q p G.freeBoundary ω)]
  exact Finset.sum_congr rfl (fun ω _ => G.fkWeight_free_transport eV eE q p ω)

/-- Pointwise free-boundary FK masses are invariant under transport. -/
theorem fkPMF_free_transport {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (ω : (G.transport eV eE).Configuration) :
    G.fkPMF hq hp1.le G.freeBoundary (G.transportConfig eV eE ω)
      = (G.transport eV eE).fkPMF hq hp1.le (G.transport eV eE).freeBoundary ω := by
  rw [LabelledMultigraph.fkPMF_apply, LabelledMultigraph.fkPMF_apply,
    G.fkWeight_free_transport eV eE q p ω, partitionFunction_free_transport G eV eE q p]

/-- Masses of transported sets agree, as finite sums of point masses. -/
theorem sum_mass_transport {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (A : Set G.Configuration) :
    (∑ ω : G.Configuration, if ω ∈ A then G.fkPMF hq hp1.le G.freeBoundary ω else 0)
      = ∑ ω : (G.transport eV eE).Configuration,
          if (G.transportConfig eV eE ω) ∈ A then
            (G.transport eV eE).fkPMF hq hp1.le (G.transport eV eE).freeBoundary ω
          else 0 := by
  classical
  rw [← Equiv.sum_comp (G.transportConfig eV eE)
    (fun ω => if ω ∈ A then G.fkPMF hq hp1.le G.freeBoundary ω else 0)]
  exact Finset.sum_congr rfl (fun ω _ => by
    rw [fkPMF_free_transport G eV eE hq hp0 hp1 ω])

/-- The transport map of configurations is measurable. -/
theorem measurable_transportConfig (G : LabelledMultigraph) (eV : V ≃ G.Vertex)
    (eE : E ≃ G.Edge) : Measurable (G.transportConfig eV eE) := by
  apply measurable_pi_iff.mpr
  intro a
  exact measurable_pi_apply (eE.symm a)

/-- The free FK *measure* is the pushforward of the transported free FK measure. -/
theorem map_transport_fkMeasure_free {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p)
    (hp1 : p < 1) :
    MeasureTheory.Measure.map (G.transportConfig eV eE)
        ((G.transport eV eE).fkMeasure hq hp1.le (G.transport eV eE).freeBoundary)
      = G.fkMeasure hq hp1.le G.freeBoundary := by
  have hm : Measurable (G.transportConfig eV eE) := measurable_transportConfig G eV eE
  have h1 : MeasureTheory.Measure.map (G.transportConfig eV eE)
        ((G.transport eV eE).fkMeasure hq hp1.le (G.transport eV eE).freeBoundary)
      = (PMF.map (G.transportConfig eV eE)
          ((G.transport eV eE).fkPMF hq hp1.le (G.transport eV eE).freeBoundary)).toMeasure :=
    PMF.toMeasure_map _ _ hm
  rw [h1, map_transport_fkPMF_free G eV eE hq hp0 hp1]
  show (G.fkPMF hq hp1.le G.freeBoundary).toMeasure = G.fkMeasure hq hp1.le G.freeBoundary
  rfl

/-- **Free-mass transport identity**: masses of an event and of its transported
preimage agree. -/
theorem fkMeasure_free_transport_apply {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p)
    (hp1 : p < 1) {A : Set G.Configuration} (hA : MeasurableSet A) :
    G.fkMeasure hq hp1.le G.freeBoundary A
      = (G.transport eV eE).fkMeasure hq hp1.le (G.transport eV eE).freeBoundary
          ((G.transportConfig eV eE) ⁻¹' A) := by
  have hm : Measurable (G.transportConfig eV eE) := measurable_transportConfig G eV eE
  have hmap := map_transport_fkMeasure_free G eV eE hq hp0 hp1
  rw [← hmap, MeasureTheory.Measure.map_apply hm hA]

end Transport

end FK.NestedMixture

#print axioms FK.NestedMixture.fkPMF_eq_of_source_target_eq
#print axioms FK.NestedMixture.partitionFunction_free_transport
#print axioms FK.NestedMixture.fkPMF_free_transport
#print axioms FK.NestedMixture.sum_mass_transport
#print axioms FK.NestedMixture.map_transport_fkMeasure_free
#print axioms FK.NestedMixture.fkMeasure_free_transport_apply
#print axioms FK.NestedMixture.fkMeasure_eq_of_source_target_eq
