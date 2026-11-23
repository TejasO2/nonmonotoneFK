import FK.Proposition42
import FK.ClosedBoundary
import CurvatureVariance.Infra.Percolation.Critical

/-!
# Coupling and subcriticality infrastructure for strong uniqueness

This file supplies two steps used in Theorem 5.1 of
Beffara--Faipeur--Oke (arXiv:2512.16486).

* Two ordered couplings with the same upper marginal are disintegrated along
  that marginal and their conditional laws are sampled independently.  The
  resulting triple has exactly the prescribed three marginals and satisfies
  both order relations almost surely.  A measurable decreasing property of
  the upper configuration is inherited by both lower configurations.
* Non-percolation is defined by finiteness of open-walk clusters in the
  vendored configuration model and proved measurable.  It is equivalent to
  existence of the finite connected closed-boundary exhaustion used in the
  paper, and that full-support event is inherited by both dominated laws.

The DLR identification of conditional probabilities, backward-martingale
convergence, tail triviality, and the extremal-simplex argument are not
assumed here; they remain separate obligations for the full theorem.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace FK

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [LE Ω]

/-- Glue two ordered measure couplings along their common second marginal.
The measurability hypothesis on the order relation is explicit so that the
almost-everywhere order conclusions can be transported through disintegration. -/
theorem exists_orderedTripleCoupling
    (μ ν ρ : Measure Ω) (γ₁ γ₂ : Measure (Ω × Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    (hγ₁fst : γ₁.map Prod.fst = μ) (hγ₁snd : γ₁.map Prod.snd = ρ)
    (hγ₂fst : γ₂.map Prod.fst = ν) (hγ₂snd : γ₂.map Prod.snd = ρ)
    (horder : MeasurableSet {z : Ω × Ω | z.1 ≤ z.2})
    (hord₁ : ∀ᵐ z ∂γ₁, z.1 ≤ z.2) (hord₂ : ∀ᵐ z ∂γ₂, z.1 ≤ z.2) :
    ∃ τ : Measure (Ω × Ω × Ω), IsProbabilityMeasure τ ∧
      τ.map (fun z => z.1) = μ ∧ τ.map (fun z => z.2.1) = ν ∧
      τ.map (fun z => z.2.2) = ρ ∧
      ∀ᵐ z ∂τ, z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
  let δ₁ : Measure (Ω × Ω) := γ₁.map Prod.swap
  let δ₂ : Measure (Ω × Ω) := γ₂.map Prod.swap
  have hδ₁fst : δ₁.fst = ρ := by
    simpa [δ₁, Measure.snd] using hγ₁snd
  have hδ₂fst : δ₂.fst = ρ := by
    simpa [δ₂, Measure.snd] using hγ₂snd
  have hdis₁ : ρ ⊗ₘ δ₁.condKernel = δ₁ := by
    rw [← hδ₁fst]
    exact δ₁.disintegrate δ₁.condKernel
  have hdis₂ : ρ ⊗ₘ δ₂.condKernel = δ₂ := by
    rw [← hδ₂fst]
    exact δ₂.disintegrate δ₂.condKernel
  let K : Kernel Ω (Ω × Ω) := δ₁.condKernel ×ₖ δ₂.condKernel
  let P : Measure (Ω × (Ω × Ω)) := ρ ⊗ₘ K
  let f : Ω × (Ω × Ω) → Ω × Ω × Ω := fun z => (z.2.1, z.2.2, z.1)
  let τ : Measure (Ω × Ω × Ω) := P.map f
  have hf : Measurable f := by fun_prop
  have hKfst : K.fst = δ₁.condKernel := by simp [K]
  have hKsnd : K.snd = δ₂.condKernel := by simp [K]
  have hleft : P.map (fun z => z.2.1) = μ := by
    calc
      P.map (fun z => z.2.1) = (ρ ⊗ₘ K.fst).snd := by
        rw [Kernel.fst_eq, Measure.compProd_map measurable_fst]
        change Measure.map (fun z : Ω × (Ω × Ω) => z.2.1) (ρ ⊗ₘ K) =
          Measure.map Prod.snd (Measure.map (Prod.map id Prod.fst) (ρ ⊗ₘ K))
        rw [Measure.map_map measurable_snd (measurable_id.prodMap measurable_fst)]
        rfl
      _ = (ρ ⊗ₘ δ₁.condKernel).snd := by rw [hKfst]
      _ = δ₁.snd := by rw [hdis₁]
      _ = γ₁.fst := by simp [δ₁]
      _ = μ := hγ₁fst
  have hright : P.map (fun z => z.2.2) = ν := by
    calc
      P.map (fun z => z.2.2) = (ρ ⊗ₘ K.snd).snd := by
        rw [Kernel.snd_eq, Measure.compProd_map measurable_snd]
        change Measure.map (fun z : Ω × (Ω × Ω) => z.2.2) (ρ ⊗ₘ K) =
          Measure.map Prod.snd (Measure.map (Prod.map id Prod.snd) (ρ ⊗ₘ K))
        rw [Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd)]
        rfl
      _ = (ρ ⊗ₘ δ₂.condKernel).snd := by rw [hKsnd]
      _ = δ₂.snd := by rw [hdis₂]
      _ = γ₂.fst := by simp [δ₂]
      _ = ν := hγ₂fst
  have hmiddle : P.map Prod.fst = ρ := by
    simpa [P, Measure.fst] using Measure.fst_compProd ρ K
  have hτleft : τ.map (fun z => z.1) = μ := by
    change (P.map f).map _ = μ
    rw [Measure.map_map (by fun_prop) hf]
    exact hleft
  have hτright : τ.map (fun z => z.2.1) = ν := by
    change (P.map f).map _ = ν
    rw [Measure.map_map (by fun_prop) hf]
    exact hright
  have hτmiddle : τ.map (fun z => z.2.2) = ρ := by
    change (P.map f).map _ = ρ
    rw [Measure.map_map (by fun_prop) hf]
    exact hmiddle
  have hδ₁ord : ∀ᵐ z ∂δ₁, z.2 ≤ z.1 := by
    exact (ae_map_iff measurable_swap.aemeasurable (measurable_swap horder)).2 hord₁
  have hδ₂ord : ∀ᵐ z ∂δ₂, z.2 ≤ z.1 := by
    exact (ae_map_iff measurable_swap.aemeasurable (measurable_swap horder)).2 hord₂
  have hκ₁ : ∀ᵐ z ∂ρ, ∀ᵐ x ∂δ₁.condKernel z, x ≤ z := by
    apply (Measure.ae_compProd_iff (measurable_swap horder)).1
    rw [hdis₁]
    exact hδ₁ord
  have hκ₂ : ∀ᵐ z ∂ρ, ∀ᵐ x ∂δ₂.condKernel z, x ≤ z := by
    apply (Measure.ae_compProd_iff (measurable_swap horder)).1
    rw [hdis₂]
    exact hδ₂ord
  have hPord : ∀ᵐ z ∂P, z.2.1 ≤ z.1 ∧ z.2.2 ≤ z.1 := by
    have hmeas : MeasurableSet {z : Ω × (Ω × Ω) |
        z.2.1 ≤ z.1 ∧ z.2.2 ≤ z.1} :=
      (horder.preimage (show Measurable (fun z : Ω × (Ω × Ω) => (z.2.1, z.1)) by
        fun_prop)).inter
      (horder.preimage (show Measurable (fun z : Ω × (Ω × Ω) => (z.2.2, z.1)) by
        fun_prop))
    apply Measure.ae_compProd_of_ae_ae hmeas
    filter_upwards [hκ₁, hκ₂] with z hz₁ hz₂
    change ∀ᵐ p ∂((δ₁.condKernel ×ₖ δ₂.condKernel) z), p.1 ≤ z ∧ p.2 ≤ z
    rw [Kernel.prod_apply]
    have hp : MeasurableSet {p : Ω × Ω | p.1 ≤ z ∧ p.2 ≤ z} :=
      (horder.preimage (show Measurable (fun p : Ω × Ω => (p.1, z)) by
        fun_prop)).inter
      (horder.preimage (show Measurable (fun p : Ω × Ω => (p.2, z)) by
        fun_prop))
    rw [Measure.ae_prod_iff_ae_ae hp]
    filter_upwards [hz₁] with x hx
    exact hz₂.mono fun y hy => ⟨hx, hy⟩
  have hτord : ∀ᵐ z ∂τ, z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
    have hmeas : MeasurableSet {z : Ω × Ω × Ω |
        z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2} :=
      (horder.preimage (show Measurable (fun z : Ω × Ω × Ω => (z.1, z.2.2)) by
        fun_prop)).inter
      (horder.preimage (show Measurable (fun z : Ω × Ω × Ω => (z.2.1, z.2.2)) by
        fun_prop))
    apply (ae_map_iff hf.aemeasurable hmeas).2
    simpa [τ, f] using hPord
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  haveI : IsProbabilityMeasure τ := by
    dsimp [τ]
    infer_instance
  exact ⟨τ, inferInstance, hτleft, hτright, hτmiddle, hτord⟩

/-- A measurable decreasing property of the common upper configuration holds
almost everywhere under both lower marginals of an ordered triple coupling. -/
theorem ae_lower_of_orderedTripleCoupling
    {Ω : Type*} [MeasurableSpace Ω] [LE Ω]
    {μ ν ρ : Measure Ω} {τ : Measure (Ω × Ω × Ω)}
    (hτμ : τ.map (fun z => z.1) = μ) (hτν : τ.map (fun z => z.2.1) = ν)
    (hτρ : τ.map (fun z => z.2.2) = ρ)
    (hord : ∀ᵐ z ∂τ, z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2)
    {B : Set Ω} (hB : MeasurableSet B) (hlower : IsLowerSet B)
    (hρB : ∀ᵐ z ∂ρ, z ∈ B) :
    (∀ᵐ x ∂μ, x ∈ B) ∧ (∀ᵐ x ∂ν, x ∈ B) := by
  have hm_upper : Measurable (fun z : Ω × Ω × Ω => z.2.2) := by fun_prop
  have hm_left : Measurable (fun z : Ω × Ω × Ω => z.1) := by fun_prop
  have hm_right : Measurable (fun z : Ω × Ω × Ω => z.2.1) := by fun_prop
  have hupper : ∀ᵐ z ∂τ, z.2.2 ∈ B := by
    apply (ae_map_iff hm_upper.aemeasurable hB).1
    rwa [hτρ]
  have hboth : ∀ᵐ z ∂τ, z.1 ∈ B ∧ z.2.1 ∈ B := by
    filter_upwards [hord, hupper] with z hz hzB
    exact ⟨hlower hz.1 hzB, hlower hz.2 hzB⟩
  constructor
  · have h := (ae_map_iff hm_left.aemeasurable hB).2 (hboth.mono fun _ h => h.1)
    rwa [hτμ] at h
  · have h := (ae_map_iff hm_right.aemeasurable hB).2 (hboth.mono fun _ h => h.2)
    rwa [hτν] at h

/-- The pointwise order on countable edge configurations is measurable. -/
lemma measurableSet_pointwiseLE_configuration {E : Type*} [Countable E] :
    MeasurableSet {z : FKLimit.Configuration E × FKLimit.Configuration E |
      z.1 ≤ z.2} := by
  change MeasurableSet {z : FKLimit.Configuration E × FKLimit.Configuration E |
    ∀ e, z.1 e ≤ z.2 e}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro e
  have hle : MeasurableSet {b : Bool × Bool | b.1 ≤ b.2} := MeasurableSet.of_discrete
  exact hle.preimage (show Measurable
    (fun z : FKLimit.Configuration E × FKLimit.Configuration E => (z.1 e, z.2 e)) by
      fun_prop)

/-- Configuration-space form of `exists_orderedTripleCoupling`. -/
theorem exists_orderedTripleCoupling_configurations
    {E : Type*} [Countable E]
    (μ ν ρ : Measure (FKLimit.Configuration E))
    (γ₁ γ₂ : Measure (FKLimit.Configuration E × FKLimit.Configuration E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    (hγ₁fst : γ₁.map Prod.fst = μ) (hγ₁snd : γ₁.map Prod.snd = ρ)
    (hγ₂fst : γ₂.map Prod.fst = ν) (hγ₂snd : γ₂.map Prod.snd = ρ)
    (hord₁ : ∀ᵐ z ∂γ₁, z.1 ≤ z.2) (hord₂ : ∀ᵐ z ∂γ₂, z.1 ≤ z.2) :
    ∃ τ : Measure (FKLimit.Configuration E × FKLimit.Configuration E ×
      FKLimit.Configuration E), IsProbabilityMeasure τ ∧
      τ.map (fun z => z.1) = μ ∧ τ.map (fun z => z.2.1) = ν ∧
      τ.map (fun z => z.2.2) = ρ ∧
      ∀ᵐ z ∂τ, z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
  exact exists_orderedTripleCoupling μ ν ρ γ₁ γ₂ hγ₁fst hγ₁snd hγ₂fst hγ₂snd
    measurableSet_pointwiseLE_configuration hord₁ hord₂

open CurvatureVariance.Infra.Percolation

variable {V : Type*} (G : SimpleGraph V)

/-- Every open cluster is finite in the open-walk configuration model. -/
def NonPercolating : Set (G.edgeSet → Bool) :=
  {ω | ∀ o, {x | OpenConnected G ω Set.univ o x}.Finite}

/-- In a connected locally finite graph, non-percolation is measurable.  The
proof uses the vendored characterization of an infinite cluster by the full
sequence of measurable arm events. -/
lemma measurableSet_nonPercolating [Countable V] [G.LocallyFinite]
    (hG : G.Connected) : MeasurableSet (NonPercolating G) := by
  unfold NonPercolating
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro o
  have hinf : MeasurableSet {ω : G.edgeSet → Bool |
      {x | OpenConnected G ω Set.univ o x}.Infinite} := by
    rw [setOf_infinite_eq_iInter_armEvent hG o]
    exact MeasurableSet.iInter fun n => measurableSet_armEvent o n
  have heq : {ω : G.edgeSet → Bool |
      {x | OpenConnected G ω Set.univ o x}.Finite} =
      {ω : G.edgeSet → Bool | {x | OpenConnected G ω Set.univ o x}.Infinite}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.Infinite, not_not]
  rw [heq]
  exact hinf.compl

/-- Finiteness of open clusters is decreasing in the edge configuration. -/
lemma isLowerSet_nonPercolating : IsLowerSet (NonPercolating G) := by
  intro ω η hωη hη o
  apply (hη o).subset
  intro x hx
  exact OpenConnected.mono_config hx hωη

/-- Both dominated laws are non-percolating when the common upper law is. -/
theorem ae_nonPercolating_of_orderedTripleCoupling
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    {μ ν ρ : Measure (G.edgeSet → Bool)} {τ : Measure ((G.edgeSet → Bool) ×
      (G.edgeSet → Bool) × (G.edgeSet → Bool))}
    (hτμ : τ.map (fun z => z.1) = μ) (hτν : τ.map (fun z => z.2.1) = ν)
    (hτρ : τ.map (fun z => z.2.2) = ρ)
    (hord : ∀ᵐ z ∂τ, z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2)
    (hρ : ∀ᵐ ω ∂ρ, ω ∈ NonPercolating G) :
    (∀ᵐ ω ∂μ, ω ∈ NonPercolating G) ∧ (∀ᵐ ω ∂ν, ω ∈ NonPercolating G) :=
  ae_lower_of_orderedTripleCoupling hτμ hτν hτρ hord
    (measurableSet_nonPercolating G hG) (isLowerSet_nonPercolating G) hρ

/-- The open subgraph is a spanning subgraph of the ambient graph. -/
lemma openGraph_le (ω : G.edgeSet → Bool) : openGraph G (openSet ω) ≤ G := by
  intro x y hxy
  rw [openGraph, SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨⟨e, he, hee⟩, -⟩ := hxy
  have hG : G.Adj x y := by
    have := e.2
    rw [hee] at this
    exact this
  exact hG

/-- `NonPercolating` is precisely the finiteness hypothesis of the existing
closed-boundary exhaustion construction. -/
lemma finiteOpenClusters_of_nonPercolating (ω : G.edgeSet → Bool)
    (hω : ω ∈ NonPercolating G) : FiniteOpenClusters (openGraph G (openSet ω)) := by
  intro v
  have heq : OpenCluster (openGraph G (openSet ω)) v =
      {x | OpenConnected G ω Set.univ v x} := by
    ext x
    rw [mem_openCluster_iff, reachable_openGraph_openSet_iff]
    simp only [Set.mem_setOf_eq]
  rw [heq]
  exact hω v

/-- Pointwise form of the simultaneous closed-boundary exhaustion used in
Theorem 5.1, now derived from the configuration-level non-percolation event. -/
theorem nonempty_closedBoundaryExhaustion_of_nonPercolating
    [Countable V] [Nonempty V] (hG : G.Preconnected) (ω : G.edgeSet → Bool)
    (hω : ω ∈ NonPercolating G) :
    Nonempty (ClosedBoundaryExhaustion G (openGraph G (openSet ω))) :=
  nonempty_closedBoundaryExhaustion_of_countable hG (openGraph_le G ω)
    (finiteOpenClusters_of_nonPercolating G ω hω)

/-- An open path starting in a region with closed ambient boundary cannot
leave that region. -/
theorem mem_region_of_openConnected {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {R : Set V} (hR : ClosedBoundary G (openGraph G (openSet ω)) R)
    {a x : V} (ha : a ∈ R) (hax : OpenConnected G ω Set.univ a x) : x ∈ R := by
  obtain ⟨p, hp⟩ := hax
  induction p with
  | nil => exact ha
  | @cons a b c hab p ih =>
    rw [isOpenIn_cons] at hp
    apply ih
    · by_contra hb
      apply hR ha hb hab
      rw [openGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨⟨s(a, b), hab⟩, hp.1.2, rfl⟩, G.ne_of_adj hab⟩
    · exact hp.2

/-- The full-support event used in Theorem 5.1: the open configuration has a
finite connected closed-boundary exhaustion. -/
def HasClosedBoundaryExhaustion : Set (G.edgeSet → Bool) :=
  {ω | Nonempty (ClosedBoundaryExhaustion G (openGraph G (openSet ω)))}

/-- Existence of a closed-boundary exhaustion is equivalent to finiteness of
all open clusters.  The reverse implication uses that an open cluster based
inside a closed-boundary region is trapped in that finite region. -/
lemma hasClosedBoundaryExhaustion_eq_nonPercolating
    [Countable V] [Nonempty V] (hG : G.Connected) :
    HasClosedBoundaryExhaustion G = NonPercolating G := by
  ext ω
  constructor
  · intro hω o
    obtain ⟨E⟩ := hω
    obtain ⟨n, hn⟩ : ∃ n, o ∈ E.region n := by
      have ho : o ∈ ⋃ n, E.region n := by rw [E.exhaustive]; exact Set.mem_univ o
      exact Set.mem_iUnion.mp ho
    apply (E.finite n).subset
    intro x hx
    exact mem_region_of_openConnected (E.closed n) hn hx
  · intro hω
    exact nonempty_closedBoundaryExhaustion_of_nonPercolating G hG.preconnected ω hω

lemma measurableSet_hasClosedBoundaryExhaustion [Countable V] [Nonempty V]
    [G.LocallyFinite] (hG : G.Connected) :
    MeasurableSet (HasClosedBoundaryExhaustion G) := by
  rw [hasClosedBoundaryExhaustion_eq_nonPercolating G hG]
  exact measurableSet_nonPercolating G hG

/-- The closed-boundary exhaustion event has full mass under both lower
marginals whenever the common upper marginal is non-percolating. -/
theorem ae_closedBoundaryExhaustion_of_orderedTripleCoupling
    [Countable V] [Nonempty V] [G.LocallyFinite] (hG : G.Connected)
    {μ ν ρ : Measure (G.edgeSet → Bool)} {τ : Measure ((G.edgeSet → Bool) ×
      (G.edgeSet → Bool) × (G.edgeSet → Bool))}
    (hτμ : τ.map (fun z => z.1) = μ) (hτν : τ.map (fun z => z.2.1) = ν)
    (hτρ : τ.map (fun z => z.2.2) = ρ)
    (hord : ∀ᵐ z ∂τ, z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2)
    (hρ : ∀ᵐ ω ∂ρ, ω ∈ NonPercolating G) :
    (∀ᵐ ω ∂μ, ω ∈ HasClosedBoundaryExhaustion G) ∧
      (∀ᵐ ω ∂ν, ω ∈ HasClosedBoundaryExhaustion G) := by
  obtain ⟨hμ, hν⟩ := ae_nonPercolating_of_orderedTripleCoupling G hG hτμ hτν hτρ hord hρ
  constructor
  · filter_upwards [hμ] with ω hω
    exact nonempty_closedBoundaryExhaustion_of_nonPercolating G hG.preconnected ω hω
  · filter_upwards [hν] with ω hω
    exact nonempty_closedBoundaryExhaustion_of_nonPercolating G hG.preconnected ω hω

end FK
