import FK.CycleBoundaryPaths

/-!
# The `q > 1` lower comparison from actual cycle paths

The finite-box certificate in `FK.CycleBoundaryPaths` is independent of the
boundary convention and of the sign of `p' - p`. This module instantiates the
actual lower open-path comparison for `q > 1` with that certificate. Thus the
raised product profile is stochastically below the DLR law, in the same
orientation as `gt_dlr_lower_of_active_cycle_devices`.

Interior wrappers derive both `0 < q` and the strict relation `p' < p` from
`0 < p < 1` and `1 < q`; neither is an additional stochastic assumption.
The final theorem combines this lower comparison with the actual geometric
star cutsets, yielding the complete two-sided `q > 1` DLR sandwich. Eventual
activation and device geometry remain explicit inputs; no strict AG shift is
asserted.
-/

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology
open FKEnhancement

noncomputable section

/-- For `q > 1`, the actual complementary-cycle paths give the lower DLR
open-path comparison. In particular, the product coordinate is based at
`p' = FK.prime q p` and is raised only on the selected cycle set. -/
theorem gt_dlr_lower_of_active_cyclePathFamily
    {V : Type*} {G : SimpleGraph V} [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (hp : (p : ℝ) ∈ Ioo 0 1) (hqR : 0 < (q : ℝ))
    (hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ))
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet)
    (cycleAdmissible : ℕ → G.edgeSet → Prop) (L : ℕ)
    (hsep : FKLimit.IsSeparatedDeviceFamily S D)
    (hcycleAdm : ∀ e ∈ S, ∀ᶠ n in atTop, cycleAdmissible n e)
    (hcycle : ∀ f ∈ S, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      D f = FK.QuasiTransitive.walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcard : ∀ f ∈ S, (D f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    FKLimit.StochasticallyDominates μ
      (FKLimit.bernoulliProduct
        (FKLimit.gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L S)) := by
  let Γ : ∀ n (_ : (exh.box n).Exterior),
      (exh.box n).edges → Set (Finset (exh.box n).edges) :=
    fun n _ e => cyclePathFamily (exh.box n) D e
  apply gt_dlr_lower_of_active_cycle_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
    S D cycleAdmissible L hsep hcycleAdm hne Γ
  · intro n η e he
    have he' : e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D
        cycleAdmissible n := mem_activeWithinFinset.mp he
    exact (cyclePathFamily_spec_of_active data Φ hinj hsep hcycle hcard η e he').1
  · intro n η e he ω hω
    have he' : e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D
        cycleAdmissible n := mem_activeWithinFinset.mp he
    exact (cyclePathFamily_spec_of_active data Φ hinj hsep hcycle hcard η e he').2.1 hω
  · intro n η e he
    exact (cyclePathFamily_spec_of_active data Φ hinj hsep hcycle hcard η e he).2.2

/-- Interior `q > 1` form. The prime inequality is proved from `1 < q`, and
the conclusion retains the exact lower-product/DLR orientation. -/
theorem gt_dlr_lower_of_active_cyclePathFamily_interior
    {V : Type*} {G : SimpleGraph V} [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ
      (lt_trans zero_lt_one hq1 : 0 < q) hp1.le)
    (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet)
    (cycleAdmissible : ℕ → G.edgeSet → Prop) (L : ℕ)
    (hsep : FKLimit.IsSeparatedDeviceFamily S D)
    (hcycleAdm : ∀ e ∈ S, ∀ᶠ n in atTop, cycleAdmissible n e)
    (hcycle : ∀ f ∈ S, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      D f = FK.QuasiTransitive.walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcard : ∀ f ∈ S, (D f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hq : 0 < q := lt_trans zero_lt_one hq1
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
    FKLimit.StochasticallyDominates μ
      (FKLimit.bernoulliProduct
        (FKLimit.gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L S)) := by
  dsimp only
  let hq : 0 < q := lt_trans zero_lt_one hq1
  let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
    (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
  exact gt_dlr_lower_of_active_cyclePathFamily exh data Φ hinj hq hp0 hp1 hq1
    hp hqR hpp hμ S D cycleAdmissible L hsep hcycleAdm hcycle hcard hne

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.gt_dlr_lower_of_active_cyclePathFamily
#print axioms FK.EnhancedTransport.gt_dlr_lower_of_active_cyclePathFamily_interior

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology
open FKEnhancement

noncomputable section

/-- Geometric `q > 1` DLR sandwich. Actual separated stars supply the upper
closed-cutset comparison and actual separated cycles supply the lower
open-path comparison. The geometric boundary hypothesis is used only for the
star singleton-class certificate; the cycle certificate is valid for every
boundary assignment. -/
theorem gt_dlr_sandwich_of_geometric_star_cyclePathFamily
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    (hΦ : FK.InfiniteVolume.ConventionTransport.IsGeometric data.geometry Φ)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ
      (lt_trans zero_lt_one hq1 : 0 < q) hp1.le)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet)
    (starAdmissible : ℕ → G.edgeSet → Prop) (Delta : ℕ)
    (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hstar : ∀ f ∈ Sstar, ∃ v : V,
      Dstar f = FK.QuasiTransitive.starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet)
    (cycleAdmissible : ℕ → G.edgeSet → Prop) (L : ℕ)
    (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.length = L ∧ Dcycle f = FK.QuasiTransitive.walkDevice c ∧
        (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hq : 0 < q := lt_trans zero_lt_one hq1
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
    FKLimit.StochasticallyDominates μ
      (FKLimit.bernoulliProduct
        (FKLimit.gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) ∧
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct
        (FKLimit.gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ := by
  dsimp only
  let hq : 0 < q := lt_trans zero_lt_one hq1
  let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
    (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
  constructor
  · exact gt_dlr_lower_of_active_cyclePathFamily exh data Φ hinj hq hp0 hp1 hq1
      hp hqR hpp hμ Scycle Dcycle cycleAdmissible L hCycle hcycleAdm hcycle
      hcycleCard hne
  · apply gt_dlr_upper_of_active_star_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Sstar Dstar starAdmissible Delta hStar hstarAdm hne
    intro n η e he
    exact data.exists_starCutset_of_active_geometric Φ hΦ hStar hstar hstarCard
      hinj η e he

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.gt_dlr_sandwich_of_geometric_star_cyclePathFamily
