import FK.FKSequentialCoupling
import FK.TripleCoupling

/-!
# Nested finite FK/Bernoulli couplings

This module constructs the actual triple used in the finite part of the
nested-box coupling lemma.  If `EΔ ⊕ EO ≃ EΣ`, the second coordinate is
sampled on `EΔ`, while its values on `EO` are copied from the common upper
configuration.  Two ordered pair couplings are glued conditionally on this
common upper configuration.

The construction proves exact marginals, support order, restriction of the
second marginal, and equality with the upper coordinate outside the smaller
edge set.  It does not assert the maximal-cutset/free-interior property: that
requires the exploration-stratum analysis and is kept separate.
-/

open scoped ENNReal BigOperators Classical

namespace FK.Exploration.NestedFiniteCoupling

open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.FKCoupling

universe u v w

/-- The independent product of two probability mass functions. -/
noncomputable def prodPMF {α : Type u} {β : Type v} (μ : PMF α) (ν : PMF β) :
    PMF (α × β) :=
  (PMF.Coupling.product μ ν).dist

lemma prodPMF_map_fst {α : Type u} {β : Type v} (μ : PMF α) (ν : PMF β) :
    (prodPMF μ ν).map Prod.fst = μ :=
  (PMF.Coupling.product μ ν).map_fst

lemma prodPMF_map_snd {α : Type u} {β : Type v} (μ : PMF α) (ν : PMF β) :
    (prodPMF μ ν).map Prod.snd = ν :=
  (PMF.Coupling.product μ ν).map_snd

@[simp] lemma prodPMF_apply {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (μ : PMF α) (ν : PMF β) (a : α) (b : β) :
    prodPMF μ ν (a, b) = μ a * ν b := by
  simp [prodPMF, PMF.Coupling.product, PMF.bind_apply, PMF.map_apply,
    tsum_fintype, Prod.ext_iff, ite_and]

/-- Join configurations along an identification of the ambient edge set with
a disjoint sum. -/
def configEquiv {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge) :
    (GD.Configuration × GO.Configuration) ≃ GS.Configuration :=
  (Equiv.sumArrowEquivProdArrow GD.Edge GO.Edge Bool).symm.trans
    (Equiv.arrowCongr e (Equiv.refl Bool))

/-- Restriction to the smaller edge set in the nested configuration. -/
def restrictΔ {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge) (ω : GS.Configuration) : GD.Configuration :=
  fun a => ω (e (Sum.inl a))

/-- Restriction to the edges on which the second configuration copies the
common upper configuration. -/
def restrictO {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge) (ω : GS.Configuration) : GO.Configuration :=
  fun o => ω (e (Sum.inr o))

@[simp] lemma restrictΔ_configEquiv {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge) (z : GD.Configuration × GO.Configuration) :
    restrictΔ e (configEquiv e z) = z.1 := by
  funext a
  simp [restrictΔ, configEquiv, Equiv.arrowCongr_apply, Function.comp_def]
  rfl

@[simp] lemma restrictO_configEquiv {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge) (z : GD.Configuration × GO.Configuration) :
    restrictO e (configEquiv e z) = z.2 := by
  funext o
  simp [restrictO, configEquiv, Equiv.arrowCongr_apply, Function.comp_def]
  rfl

lemma configEquiv_symm_apply {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge) (ω : GS.Configuration) :
    (configEquiv e).symm ω = (restrictΔ e ω, restrictO e ω) := by
  apply Prod.ext
  · rw [← restrictΔ_configEquiv e ((configEquiv e).symm ω)]
    simp
  · rw [← restrictO_configEquiv e ((configEquiv e).symm ω)]
    simp

/-- Mass of a pushforward along an equivalence. -/
lemma map_equiv_apply {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (e : α ≃ β) (μ : PMF α) (b : β) : μ.map e b = μ (e.symm b) := by
  rw [PMF.map_apply, tsum_fintype]
  rw [← e.symm.sum_comp]
  simp

/-- A full product configuration law split along an edge equivalence. -/
noncomputable def splitLaw {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    (μΔ : PMF GD.Configuration) (μO : PMF GO.Configuration) : PMF GS.Configuration :=
  (prodPMF μΔ μO).map (configEquiv e)

lemma map_restrictΔ_splitLaw {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    (μΔ : PMF GD.Configuration) (μO : PMF GO.Configuration) :
    (splitLaw e μΔ μO).map (restrictΔ e) = μΔ := by
  rw [splitLaw, PMF.map_comp]
  rw [show (restrictΔ e) ∘ (configEquiv e) = Prod.fst by
    funext z
    exact restrictΔ_configEquiv e z]
  exact prodPMF_map_fst μΔ μO

lemma map_restrictO_splitLaw {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    (μΔ : PMF GD.Configuration) (μO : PMF GO.Configuration) :
    (splitLaw e μΔ μO).map (restrictO e) = μO := by
  rw [splitLaw, PMF.map_comp]
  rw [show (restrictO e) ∘ (configEquiv e) = Prod.snd by
    funext z
    exact restrictO_configEquiv e z]
  exact prodPMF_map_snd μΔ μO

/-- Splitting independent Bernoulli products gives the ambient product. -/
theorem splitLaw_bernoulliProductPMF {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge) {p : NNReal} (hp : p ≤ 1) :
    splitLaw e (GD.bernoulliProductPMF hp) (GO.bernoulliProductPMF hp) =
      GS.bernoulliProductPMF hp := by
  apply PMF.ext
  intro ω
  rw [splitLaw, map_equiv_apply (configEquiv e) _ ω,
    configEquiv_symm_apply]
  simp only [bernoulliProductPMF_apply]
  rw [prodPMF_apply]
  simp only [bernoulliProductPMF_apply, edgeWeight, restrictΔ, restrictO]
  norm_cast
  exact (Fintype.prod_sum_type
    (fun x => if ω (e x) = true then p else 1 - p)).symm.trans
      (e.prod_comp (fun a => if ω a = true then p else 1 - p))

/-- Extend a smaller ordered pair by independent upper bits.  The smaller
coordinate is coupled on `EΔ` and copied from the upper coordinate on `EO`. -/
noncomputable def extendPairDist {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μΔ ρΔ : PMF GD.Configuration} (c : PMF.OrderedCoupling μΔ ρΔ)
    (ρO : PMF GO.Configuration) : PMF (GS.Configuration × GS.Configuration) :=
  c.dist.bind fun z => ρO.map fun o =>
    (configEquiv e (z.1, o), configEquiv e (z.2, o))

lemma extendPairDist_map_fst {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μΔ ρΔ : PMF GD.Configuration} (c : PMF.OrderedCoupling μΔ ρΔ)
    (ρO : PMF GO.Configuration) :
    (extendPairDist e c ρO).map Prod.fst = splitLaw e μΔ ρO := by
  rw [extendPairDist, PMF.map_bind]
  have h (z : GD.Configuration × GD.Configuration) :
      ((ρO.map fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o))).map
        Prod.fst) = ρO.map (fun o => configEquiv e (z.1, o)) := by
    rw [PMF.map_comp]
    rfl
  simp_rw [h]
  have hprod (z : GD.Configuration × GD.Configuration) :
      (ρO.map fun o => configEquiv e (z.1, o)) =
        (prodPMF (PMF.pure z.1) ρO).map (configEquiv e) := by
    simp [prodPMF, PMF.Coupling.product]
    rw [PMF.map_comp]
    rfl
  simp_rw [hprod]
  change c.dist.bind (fun z => (prodPMF (PMF.pure z.1) ρO).map (configEquiv e)) = _
  change c.dist.bind ((fun a : GD.Configuration =>
    (prodPMF (PMF.pure a) ρO).map (configEquiv e)) ∘ Prod.fst) = _
  rw [← PMF.bind_map, c.map_fst]
  simp [splitLaw, prodPMF, PMF.Coupling.product, PMF.map_bind, PMF.map_comp]

lemma extendPairDist_map_snd {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μΔ ρΔ : PMF GD.Configuration} (c : PMF.OrderedCoupling μΔ ρΔ)
    (ρO : PMF GO.Configuration) :
    (extendPairDist e c ρO).map Prod.snd = splitLaw e ρΔ ρO := by
  rw [extendPairDist, PMF.map_bind]
  have h (z : GD.Configuration × GD.Configuration) :
      ((ρO.map fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o))).map
        Prod.snd) = ρO.map (fun o => configEquiv e (z.2, o)) := by
    rw [PMF.map_comp]
    rfl
  simp_rw [h]
  have hprod (z : GD.Configuration × GD.Configuration) :
      (ρO.map fun o => configEquiv e (z.2, o)) =
        (prodPMF (PMF.pure z.2) ρO).map (configEquiv e) := by
    simp [prodPMF, PMF.Coupling.product]
    rw [PMF.map_comp]
    rfl
  simp_rw [hprod]
  change c.dist.bind (fun z => (prodPMF (PMF.pure z.2) ρO).map (configEquiv e)) = _
  change c.dist.bind ((fun a : GD.Configuration =>
    (prodPMF (PMF.pure a) ρO).map (configEquiv e)) ∘ Prod.snd) = _
  rw [← PMF.bind_map, c.map_snd]
  simp [splitLaw, prodPMF, PMF.Coupling.product, PMF.map_bind, PMF.map_comp]

/-- Restricting both members of the extended pair to the smaller graph
recovers the original pair law exactly. -/
theorem extendPairDist_map_restrictΔ_pair {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μΔ ρΔ : PMF GD.Configuration} (c : PMF.OrderedCoupling μΔ ρΔ)
    (ρO : PMF GO.Configuration) :
    (extendPairDist e c ρO).map
      (fun z => (restrictΔ e z.1, restrictΔ e z.2)) = c.dist := by
  rw [extendPairDist, PMF.map_bind]
  have h (z : GD.Configuration × GD.Configuration) :
      ((ρO.map fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o))).map
        (fun w => (restrictΔ e w.1, restrictΔ e w.2))) = PMF.pure z := by
    rw [PMF.map_comp]
    rw [show ((fun w : GS.Configuration × GS.Configuration =>
          (restrictΔ e w.1, restrictΔ e w.2)) ∘
        (fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o))) =
        Function.const GO.Configuration z) by
      funext o
      simp]
    exact PMF.map_const ρO z
  simp_rw [h]
  exact c.dist.bind_pure

lemma extendPairDist_support {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μΔ ρΔ : PMF GD.Configuration} (c : PMF.OrderedCoupling μΔ ρΔ)
    (ρO : PMF GO.Configuration) {z : GS.Configuration × GS.Configuration}
    (hz : z ∈ (extendPairDist e c ρO).support) :
    z.1 ≤ z.2 ∧ restrictO e z.1 = restrictO e z.2 := by
  rw [extendPairDist, PMF.mem_support_bind_iff] at hz
  obtain ⟨x, hx, hz⟩ := hz
  rw [PMF.mem_support_map_iff] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  constructor
  · intro a
    rcases e.surjective a with ⟨j, rfl⟩
    cases j with
    | inl a =>
      change restrictΔ e (configEquiv e (x.1, o)) a ≤
        restrictΔ e (configEquiv e (x.2, o)) a
      rw [restrictΔ_configEquiv, restrictΔ_configEquiv]
      exact c.ordered x hx a
    | inr o' =>
      change restrictO e (configEquiv e (x.1, o)) o' ≤
        restrictO e (configEquiv e (x.2, o)) o'
      rw [restrictO_configEquiv, restrictO_configEquiv]
  · funext o'
    change restrictO e (configEquiv e (x.1, o)) o' =
      restrictO e (configEquiv e (x.2, o)) o'
    rw [restrictO_configEquiv, restrictO_configEquiv]

/-- The extended ordered pair, with exact full-configuration marginals. -/
noncomputable def extendOrderedCoupling {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μΔ ρΔ : PMF GD.Configuration} (c : PMF.OrderedCoupling μΔ ρΔ)
    (ρO : PMF GO.Configuration) :
    PMF.OrderedCoupling (splitLaw e μΔ ρO) (splitLaw e ρΔ ρO) where
  dist := extendPairDist e c ρO
  map_fst := extendPairDist_map_fst e c ρO
  map_snd := extendPairDist_map_snd e c ρO
  ordered _ hz := (extendPairDist_support e c ρO hz).1

/-- Glue a full ordered pair to a nested ordered pair through their common
full upper configuration. -/
noncomputable def nestedOrderedTriple {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μS : PMF GS.Configuration} {μΔ ρΔ : PMF GD.Configuration}
    {ρO : PMF GO.Configuration}
    (cS : PMF.OrderedCoupling μS (splitLaw e ρΔ ρO))
    (cΔ : PMF.OrderedCoupling μΔ ρΔ) :
    PMF.OrderedTripleCoupling μS (splitLaw e μΔ ρO) (splitLaw e ρΔ ρO) :=
  PMF.OrderedCoupling.glue cS (extendOrderedCoupling e cΔ ρO)

/-- The smaller restriction of the nested second marginal is exactly the
original smaller law. -/
theorem nestedOrderedTriple_map_snd_restrictΔ {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μS : PMF GS.Configuration} {μΔ ρΔ : PMF GD.Configuration}
    {ρO : PMF GO.Configuration}
    (cS : PMF.OrderedCoupling μS (splitLaw e ρΔ ρO))
    (cΔ : PMF.OrderedCoupling μΔ ρΔ) :
    ((nestedOrderedTriple e cS cΔ).dist.map
      (fun z => restrictΔ e z.2.1)) = μΔ := by
  rw [show (fun z : GS.Configuration × GS.Configuration × GS.Configuration =>
      restrictΔ e z.2.1) = (restrictΔ e) ∘ (fun z => z.2.1) from rfl]
  rw [← PMF.map_comp, (nestedOrderedTriple e cS cΔ).map_snd]
  exact map_restrictΔ_splitLaw e μΔ ρO

/-- The joint smaller restriction of the second and upper coordinates is
exactly the original ordered pair, hence can serve directly as the input to
smaller-graph free-interior and equation-(9) theorems. -/
theorem nestedOrderedTriple_map_snd_thd_restrictΔ_pair
    {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μS : PMF GS.Configuration} {μΔ ρΔ : PMF GD.Configuration}
    {ρO : PMF GO.Configuration}
    (cS : PMF.OrderedCoupling μS (splitLaw e ρΔ ρO))
    (cΔ : PMF.OrderedCoupling μΔ ρΔ) :
    (nestedOrderedTriple e cS cΔ).dist.map
      (fun z => (restrictΔ e z.2.1, restrictΔ e z.2.2)) = cΔ.dist := by
  change (PMF.Coupling.glueDist cS.toCoupling
    (extendOrderedCoupling e cΔ ρO).toCoupling).map _ = cΔ.dist
  rw [show (fun z : GS.Configuration × GS.Configuration × GS.Configuration =>
      (restrictΔ e z.2.1, restrictΔ e z.2.2)) =
      (fun w : GS.Configuration × GS.Configuration =>
        (restrictΔ e w.1, restrictΔ e w.2)) ∘ (fun z => (z.2.1, z.2.2)) from rfl]
  rw [← PMF.map_comp, PMF.Coupling.map_glueDist_snd_thd]
  exact extendPairDist_map_restrictΔ_pair e cΔ ρO

/-- Outside the smaller edge set the nested second coordinate is literally
equal to the common upper coordinate on every support point. -/
theorem nestedOrderedTriple_outside {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μS : PMF GS.Configuration} {μΔ ρΔ : PMF GD.Configuration}
    {ρO : PMF GO.Configuration}
    (cS : PMF.OrderedCoupling μS (splitLaw e ρΔ ρO))
    (cΔ : PMF.OrderedCoupling μΔ ρΔ)
    {z : GS.Configuration × GS.Configuration × GS.Configuration}
    (hz : z ∈ (nestedOrderedTriple e cS cΔ).dist.support) :
    restrictO e z.2.1 = restrictO e z.2.2 := by
  have hp : (z.2.1, z.2.2) ∈ (extendOrderedCoupling e cΔ ρO).dist.support :=
    PMF.Coupling.pair_snd_thd_mem_support_of_glue_support
      cS.toCoupling (extendOrderedCoupling e cΔ ρO).toCoupling hz
  exact (extendPairDist_support e cΔ ρO hp).2

end FK.Exploration.NestedFiniteCoupling

namespace FK.Exploration.NestedFiniteCoupling

open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.FKCoupling
open MeasureTheory

/-- Actual finite FK/Nested-FK/Bernoulli triple.  The graph on `EO` carries
only independent upper bits.  All boundary setoids on the two FK graphs are
allowed. -/
noncomputable def fkNestedOrderedTriple
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.OrderedTripleCoupling
      ((finIndexedGraph VS nS sS tS).fkPMF hq hp₁.le ξ)
      (splitLaw e ((finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ)
        (GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)))
      (splitLaw e
        ((finIndexedGraph VD nD sD tD).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le))
        (GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))) := by
  let hr := upperRateNN_le_one hq hp₁.le
  let cS : PMF.OrderedCoupling
      ((finIndexedGraph VS nS sS tS).fkPMF hq hp₁.le ξ)
      (splitLaw e
        ((finIndexedGraph VD nD sD tD).bernoulliProductPMF hr)
        (GO.bernoulliProductPMF hr)) := by
    rw [splitLaw_bernoulliProductPMF e hr]
    exact fkUpperOrderedCoupling sS tS ξ hq hp₀ hp₁
  exact nestedOrderedTriple e cS (fkUpperOrderedCoupling sD tD τ hq hp₀ hp₁)

/-- The first marginal is the actual FK law on the larger graph. -/
theorem fkNestedOrderedTriple_map_fst
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.map
      (fun z => z.1) = (finIndexedGraph VS nS sS tS).fkPMF hq hp₁.le ξ :=
  (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).map_fst

/-- Restriction of the second marginal is the actual FK law on the smaller
nested graph, with its own arbitrary boundary setoid. -/
theorem fkNestedOrderedTriple_map_snd_restrictΔ
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.map
      (fun z => restrictΔ e z.2.1) =
        (finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ := by
  exact nestedOrderedTriple_map_snd_restrictΔ e _ _

/-- The third marginal is the actual Bernoulli product on the larger graph. -/
theorem fkNestedOrderedTriple_map_thd
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.map
      (fun z => z.2.2) =
        (finIndexedGraph VS nS sS tS).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le) := by
  calc
    _ = splitLaw e
        ((finIndexedGraph VD nD sD tD).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le))
        (GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)) :=
      (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).map_thd
    _ = _ := splitLaw_bernoulliProductPMF e (upperRateNN_le_one hq hp₁.le)

/-- Both actual configurations are supported below their common upper
configuration. -/
theorem fkNestedOrderedTriple_ordered
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    {z : (finIndexedGraph VS nS sS tS).Configuration ×
      (finIndexedGraph VS nS sS tS).Configuration ×
      (finIndexedGraph VS nS sS tS).Configuration}
    (hz : z ∈ (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.support) :
    z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 :=
  ⟨(fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).rel_fst z hz,
    (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).rel_snd z hz⟩

/-- Outside the smaller graph the second FK coordinate has no independently
sampled bits: it agrees with the common upper configuration. -/
theorem fkNestedOrderedTriple_outside
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    {z : (finIndexedGraph VS nS sS tS).Configuration ×
      (finIndexedGraph VS nS sS tS).Configuration ×
      (finIndexedGraph VS nS sS tS).Configuration}
    (hz : z ∈ (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.support) :
    restrictO e z.2.1 = restrictO e z.2.2 := by
  exact nestedOrderedTriple_outside e _ _ hz

/-- In the actual FK instantiation, the second/upper pair restricted to the
smaller edge set is literally the existing finite FK/upper pair. -/
theorem fkNestedOrderedTriple_map_snd_thd_restrictΔ_pair
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.map
      (fun z => (restrictΔ e z.2.1, restrictΔ e z.2.2)) =
        fkUpperPair sD tD τ hq hp₀ hp₁ := by
  exact nestedOrderedTriple_map_snd_thd_restrictΔ_pair e _ _


/-- **Conditional nested equation (9).**  The observed event is pulled back
from the smaller graph, and the only remaining coupling premise is equality
of the two good intersections (the common free-interior law).  In particular,
no separate second-marginal restriction identity is required: it is proved by
`fkNestedOrderedTriple_map_snd_restrictΔ_pair`. -/
theorem fkNestedOrderedTriple_abs_sub_le_of_good
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set (finIndexedGraph VS nS sS tS).Configuration)
    (A C : Set (finIndexedGraph VD nD sD tD).Configuration)
    (hBA : B = restrictΔ e ⁻¹' A)
    (hgood :
      (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.toMeasure
        ((fun z => z.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.toMeasure
        ((fun z => z.2.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C))) :
    |((finIndexedGraph VS nS sS tS).fkPMF hq hp₁.le ξ).toMeasure.real B -
        ((finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ).toMeasure.real A| ≤
      ((finIndexedGraph VS nS sS tS).bernoulliProductPMF
        (upperRateNN_le_one hq hp₁.le)).toMeasure.real (restrictΔ e ⁻¹' C)ᶜ := by
  let t := fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁
  have hrestr : Measurable (restrictΔ e) := by
    fun_prop
  have hbase := t.equation_nine_abs_bound (A := B) (B := B)
    (C := restrictΔ e ⁻¹' C) MeasurableSet.of_discrete MeasurableSet.of_discrete
    MeasurableSet.of_discrete hgood
  have hsecond :
      (splitLaw e ((finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ)
        (GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))).toMeasure.real B =
      ((finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ).toMeasure.real A := by
    rw [hBA]
    apply congrArg ENNReal.toReal
    calc
      _ = (Measure.map (restrictΔ e)
          (splitLaw e ((finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ)
            (GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))).toMeasure) A := by
          rw [Measure.map_apply hrestr MeasurableSet.of_discrete]
      _ = _ := by
        have hmap := map_restrictΔ_splitLaw e
          ((finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ)
          (GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))
        have hmap' := congrArg PMF.toMeasure hmap
        rw [← PMF.toMeasure_map _ _ hrestr] at hmap'
        rw [hmap']
  rw [hsecond] at hbase
  rw [splitLaw_bernoulliProductPMF e (upperRateNN_le_one hq hp₁.le)] at hbase
  exact hbase


end FK.Exploration.NestedFiniteCoupling
