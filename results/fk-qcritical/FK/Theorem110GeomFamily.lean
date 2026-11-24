import FK.Theorem110Strassen
import FK.StrassenCountable

/-!
# Theorem 1.10 over the *geometrically realizable* FK family

Stage 21, direction 8 (`m1`, swarm `smwu4rrf3`).

The paper's family `⋃_Φ 𝒢^Φ ∪ 𝒲` (arXiv:2512.16486v1) ranges over boundary
conditions *induced by an exterior configuration*, which in this development is
the predicate `IsGeometric data.geometry Φ` of `FK/ConventionTransport.lean`
(Proposition 1.6 of the paper: merge open exterior components, separate distinct
finite exterior components).

`FK.InfiniteVolume.FKFamily` instead unions over *all* measurable setoid-valued
assignments.  That family is strictly larger, and
`FK.InfiniteVolume.Scope.fkFamily_oneEdge_not_existsUnique` proves the difference
is not cosmetic: on the one-edge exhaustion at `q = p = 1/2` (where `p_c = 1`,
`Scope.criticalProb_twoVertex`) the unrestricted family has two distinct
members, produced by the free and the fully wired boundary setoid — and
`Scope.not_isGeometric_wiredConstantAssignment` shows the wired one is not
geometric.

This file supplies the corrected family and the corresponding assembly:

* `FKFamilyGeom` — the union of the DLR classes of geometric conventions with
  the weak limits of geometric conventions;
* `exists_isFKLimit_of_geometric_extremal` — an extremal DLR law of a geometric
  convention is a weak limit of *that* geometric convention (the witness
  sequence `n ↦ Φ.partition n (η n)` is the geometric one, so Proposition 1.8(1)
  is available inside the geometric class);
* `eq_of_unique_geometricFKLimit` — a singleton geometric limit class forces the
  whole geometric family to be that point (Choquet over the geometric class);
* `theorem_1_10_geometric_family` — Theorem 1.10 for the geometric family, with
  the domination input in its proved increasing-event form and with
  Theorem 5.1 / Proposition 1.8(2) stated over geometric conventions only.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal unitInterval

namespace FK.InfiniteVolume

open FK.InfiniteVolume.ConventionTransport

universe u

section GeomFamily

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- The subtype of geometrically realizable boundary conventions of one box
data. -/
abbrev GeomConvention (exh : BoxExhaustion.{u, u} G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) :=
  {Φ : BoundaryAssignment exh.box // IsGeometric data.geometry Φ}

/-- **Geometric extremal DLR laws are weak limits of the same geometric
convention.**  This is Proposition 1.8(1) with the witness sequence kept inside
the geometric class: the proof of `mem_fkLimitMeasures_of_extremal_dlr`
produces exactly `fun n => Φ.partition n (η n)`, and `Φ` is geometric. -/
theorem exists_isFKLimit_of_geometric_extremal (exh : BoxExhaustion.{u, u} G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryAssignment exh.box) (hΦ : IsGeometric data.geometry Φ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration G.edgeSet) =>
        (η : Measure (Configuration G.edgeSet))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration G.edgeSet))) :
    ∃ Φ' : GeomConvention exh data, ∃ η : ∀ n, (exh.box n).Exterior,
      IsFKLimit exh hq hp (fun n => Φ'.1.partition n (η n)) μ := by
  have hae := tendsto_ae_exteriorConditionalLaw_probabilityMeasure_of_extremal_dlr
    exh Φ hq hp μ hμ hext
  obtain ⟨ω, hω⟩ := hae.exists
  let η : ∀ n, (exh.box n).Exterior := fun n =>
    FKLimit.exteriorRestriction (exh.box n).edges ω
  exact ⟨⟨Φ, hΦ⟩, η,
    (tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw exh hq hp Φ.partition η μ).2 hω⟩

/-- A weak limit taken along a *geometrically realizable* convention: the
boundary partition at box `n` is the one induced by an exterior configuration
`η n` under a geometric assignment `Φ`.  This is the paper's `𝒲` restricted to
its boundary conditions. -/
def IsGeometricFKLimit (exh : BoxExhaustion.{u, u} G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration G.edgeSet)) : Prop :=
  ∃ (Φ : GeomConvention exh data) (η : ∀ n, (exh.box n).Exterior),
    IsFKLimit exh hq hp (fun n => Φ.1.partition n (η n)) μ

/-- The paper's total family at `(p,q)` for a fixed box geometry: the union of
the DLR classes of the geometrically realizable conventions with the geometric
weak limits. -/
noncomputable def FKFamilyGeom (exh : BoxExhaustion.{u, u} G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    Set (ProbabilityMeasure (Configuration G.edgeSet)) :=
  (⋃ Φ : GeomConvention exh data, DLRMeasures exh Φ.1 hq hp) ∪
    {μ | IsGeometricFKLimit exh data hq hp μ}

theorem mem_fkFamilyGeom_of_mem_dlr {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, u} G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    {Φ : GeomConvention exh data} {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ DLRMeasures exh Φ.1 hq hp) : μ ∈ FKFamilyGeom exh data hq hp :=
  Or.inl (Set.mem_iUnion.mpr ⟨Φ, hμ⟩)

theorem mem_fkFamilyGeom_of_isGeometricFKLimit {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, u} G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsGeometricFKLimit exh data hq hp μ) : μ ∈ FKFamilyGeom exh data hq hp :=
  Or.inr hμ

/-! ## The geometric family sits inside the unrestricted family -/

/-- Every geometric convention is a measurable boundary assignment, and every
geometric limit is an FK limit, so the geometric family is a subfamily of
`FKFamily`.  This is the precise sense in which the previous stage's
unrestricted family was "stronger": the claim is stronger, and
`FK.InfiniteVolume.Scope.fkFamily_oneEdge_not_existsUnique` shows it is false. -/
theorem fkFamilyGeom_subset_fkFamily {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, u} G.edgeSet) (data : SimpleGraphBoxData G exh.box) :
    FKFamilyGeom exh data hq hp ⊆ FKFamily exh hq hp := by
  intro ν hν
  rcases hν with hν | hν
  · obtain ⟨Φ, hΦ⟩ := Set.mem_iUnion.mp hν
    exact mem_fkFamily_of_mem_dlr hq hp exh hΦ
  · obtain ⟨Φ, η, hlim⟩ := hν
    exact mem_fkFamily_of_mem_fkLimit hq hp exh ⟨fun n => Φ.1.partition n (η n), hlim⟩

/-- Geometric limits are FK limits. -/
theorem isGeometricFKLimit.isFKLimit {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, u} G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsGeometricFKLimit exh data hq hp μ) :
    μ ∈ FKLimitMeasures exh hq hp := by
  obtain ⟨Φ, η, hlim⟩ := hμ
  exact ⟨fun n => Φ.1.partition n (η n), hlim⟩

/-- **A singleton geometric limit class forces the geometric family to be a
singleton** (Proposition 1.8(1) plus the tail Choquet decomposition, both inside
the geometric class). -/
theorem eq_of_unique_geometricFKLimit {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, u} G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    {μ₀ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hW : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      IsGeometricFKLimit exh data hq hp μ → μ = μ₀) :
    ∀ ν : ProbabilityMeasure (Configuration G.edgeSet),
      ν ∈ FKFamilyGeom exh data hq hp → ν = μ₀ := by
  intro ν hν
  rcases hν with hν | hν
  · obtain ⟨Φ, hν⟩ := Set.mem_iUnion.mp hν
    refine eq_dlr_of_extremal_unique exh Φ.1 hq hp ν μ₀ hν ?_
    intro ξ hξ
    obtain ⟨η, hη, hcoe⟩ := hξ.1
    have hξ' : FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration G.edgeSet) =>
          (η : Measure (Configuration G.edgeSet))) '' DLRMeasures exh Φ.1 hq hp)
        (η : Measure (Configuration G.edgeSet)) := by
      have hcast : (η : Measure (Configuration G.edgeSet)) =
          (ξ : Measure (Configuration G.edgeSet)) := hcoe
      rw [hcast]
      exact hξ
    obtain ⟨Φ', hlim⟩ := exists_isFKLimit_of_geometric_extremal exh data hq hp Φ.1 Φ.2
      η hη hξ'
    have hημ : η = μ₀ := hW η ⟨Φ', hlim⟩
    have hval : (η : Measure (Configuration G.edgeSet)) =
        (μ₀ : Measure (Configuration G.edgeSet)) := congrArg
      (fun x : ProbabilityMeasure (Configuration G.edgeSet) =>
        (x : Measure (Configuration G.edgeSet))) hημ
    exact Subtype.ext (hcoe.symm.trans hval)
  · exact hW ν hν

/-- **Theorem 1.10 over the geometrically realizable family.**

Inputs, all stated over geometric conventions only:

* `hstoch` — the increasing-event comparison of Theorem 1.2 / Theorem 1.4(1)
  against Bernoulli percolation at `s < p_c` (the order coupling is *derived*
  from it by Strassen, `exists_orderedCoupling_percolation_iff`);
* `h5_1` — Theorem 5.1 of the paper: one convention class is a singleton;
* `h518` — Proposition 1.8(2): every geometric weak limit is Gibbs for that
  convention.

Conclusion: strong uniqueness in the geometric family, and almost-sure
non-percolation of the unique measure. -/
theorem theorem_1_10_geometric_family [G.LocallyFinite] (hG : G.Connected)
    (exh : BoxExhaustion.{u, u} G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    (hne : ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      IsGeometricFKLimit exh data hq hp μ)
    (hstoch : ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      IsGeometricFKLimit exh data hq hp φ → BernoulliDominates G s φ)
    {Φ₀ : GeomConvention exh data} {μ₀ : ProbabilityMeasure (Configuration G.edgeSet)}
    (h5_1 : DLRMeasures exh Φ₀.1 hq hp = {μ₀})
    (h518 : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      IsGeometricFKLimit exh data hq hp μ → μ ∈ DLRMeasures exh Φ₀.1 hq hp) :
    (∃! μ : ProbabilityMeasure (Configuration G.edgeSet),
        μ ∈ FKFamilyGeom exh data hq hp) ∧
      ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)), ω ∈ NonPercolating G := by
  have hlim : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      IsGeometricFKLimit exh data hq hp μ → μ = μ₀ := by
    intro μ hμ
    have hmem := h518 μ hμ
    rw [h5_1] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have hfam : ∀ ν : ProbabilityMeasure (Configuration G.edgeSet),
      ν ∈ FKFamilyGeom exh data hq hp → ν = μ₀ :=
    eq_of_unique_geometricFKLimit hq hp exh data hlim
  have hμ₀ : μ₀ ∈ FKFamilyGeom exh data hq hp :=
    mem_fkFamilyGeom_of_mem_dlr hq hp exh data (by rw [h5_1]; exact Set.mem_singleton _)
  refine ⟨⟨μ₀, hμ₀, fun ν hν => hfam ν hν⟩, ?_⟩
  obtain ⟨μ, hμ⟩ := hne
  have hμ₀ : μ = μ₀ := hlim μ hμ
  have hper : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ NonPercolating G :=
    ae_nonPercolating_of_bernoulli_domination hG hs (hstoch μ hμ)
  rwa [hμ₀] at hper

end GeomFamily

end FK.InfiniteVolume
