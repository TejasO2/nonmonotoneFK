import FK.CycleBoundaryLowerPaths

/-!
# Geometric active-device comparisons with canonical finite-box admissibility

The active-device activation predicate already requires a whole device to lie
in the current finite box.  This module makes that source-geometric condition
the admissibility predicate as well, and proves its eventual validity from the
box exhaustion.  No extra activation hypothesis is left to the caller.

Actual separated incidence stars and actual separated cycle walks then give
both DLR sandwiches, in both prime directions.  The quasi-transitive corollaries
construct these families from the existing packing theorems.  The results are
stochastic comparisons for a supplied DLR law, not strict critical-point shifts.
-/

open Set Filter
open scoped SimpleGraph Sym2 Classical BigOperators Topology

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval
open FKEnhancement
open FK.InfiniteVolume

noncomputable section

/-- The canonical finite-volume admissibility condition: the whole selected
finite device is contained in the current box.  Complete-device activation
also checks the pivot and selected-set membership separately. -/
def ContainedAdmissible {E : Type*} (exh : BoxExhaustion E)
    (D : E → Finset E) : ℕ → E → Prop :=
  fun n e => D e ⊆ (exh.box n).edges

/-- Finite-device containment is eventually valid on every box exhaustion. -/
lemma eventually_containedAdmissible {E : Type*} (exh : BoxExhaustion E)
    (D : E → Finset E) (e : E) :
    ∀ᶠ n in atTop, ContainedAdmissible exh D n e := by
  exact exh.eventually_subset (D e)

/-- With canonical containment admissibility, activation is exactly membership
of the pivot and its whole device in the box, together with selection in `S`. -/
lemma mem_activeEdges_containedAdmissible {E : Type*} (exh : BoxExhaustion E)
    (S : Set E) (D : E → Finset E) (n : ℕ) (e : E) :
    e ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D
        (ContainedAdmissible exh D) n ↔
      e ∈ (exh.box n).edges ∧ e ∈ S ∧ D e ⊆ (exh.box n).edges := by
  rw [FKLimit.mem_activeEdges]
  change (e ∈ (exh.box n).edges ∧ e ∈ S ∧ D e ⊆ (exh.box n).edges ∧
    D e ⊆ (exh.box n).edges) ↔ _
  tauto

/-- Separation reduces canonical activation to the two source-geometric
conditions: selection of the pivot and containment of its whole device.
The pivot's own box membership follows from `e ∈ D e`. -/
lemma mem_activeEdges_containedAdmissible_of_isSeparated {E : Type*}
    (exh : BoxExhaustion E) {S : Set E} {D : E → Finset E}
    (hsep : FKLimit.IsSeparatedDeviceFamily S D) (n : ℕ) (e : E) :
    e ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D
        (ContainedAdmissible exh D) n ↔
      e ∈ S ∧ D e ⊆ (exh.box n).edges := by
  rw [mem_activeEdges_containedAdmissible]
  constructor
  · rintro ⟨_hebox, heS, hD⟩
    exact ⟨heS, hD⟩
  · rintro ⟨heS, hD⟩
    exact ⟨hD (hsep e heS).1, heS, hD⟩

/-- Every pivot in a separated finite-device family is eventually activated
under canonical finite-box containment admissibility. -/
lemma eventually_mem_activeEdges_containedAdmissible {E : Type*}
    (exh : BoxExhaustion E) {S : Set E} {D : E → Finset E}
    (hsep : FKLimit.IsSeparatedDeviceFamily S D) {e : E} (heS : e ∈ S) :
    ∀ᶠ n in atTop, e ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D
      (ContainedAdmissible exh D) n := by
  filter_upwards [exh.eventually_subset (D e)] with n hn
  exact (mem_activeEdges_containedAdmissible_of_isSeparated exh hsep n e).mpr
    ⟨heS, hn⟩

/-- Interior `q < 1` geometric DLR sandwich with no additional admissibility
input.  Actual incidence stars give the lower closed-cutset comparison and
actual complementary cycle paths give the upper open-path comparison. -/
theorem lt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    [Countable G.edgeSet]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp1.le)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V,
      Dstar f = QuasiTransitive.starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.length = L ∧ Dcycle f = QuasiTransitive.walkDevice c ∧
        (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
      (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
    FKLimit.StochasticallyDominates μ
      (FKLimit.bernoulliProduct
        (FKLimit.ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct
        (FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  dsimp only
  let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
    (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
  constructor
  · apply lt_dlr_lower_of_active_star_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Sstar Dstar (ContainedAdmissible exh Dstar) Delta hStar
        (fun e _ => eventually_containedAdmissible exh Dstar e) hne
    intro n η e he
    exact data.exists_starCutset_of_active_geometric Φ hΦ hStar hstar hstarCard
      hinj η e he
  · exact lt_dlr_upper_of_active_cyclePathFamily exh data Φ hinj hq hp0 hp1 hq1
      hp hqR hpp hμ Scycle Dcycle (ContainedAdmissible exh Dcycle) L hCycle
        (fun e _ => eventually_containedAdmissible exh Dcycle e) hcycle
        hcycleCard hne

/-- Interior `q > 1` geometric DLR sandwich using the same canonical
finite-box containment admissibility.  Cycle paths are now the lower
comparison and incidence-star cutsets are the upper comparison. -/
theorem gt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    [Countable G.edgeSet]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ DLRMeasures exh Φ (lt_trans zero_lt_one hq1 : 0 < q) hp1.le)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V,
      Dstar f = QuasiTransitive.starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      c.length = L ∧ Dcycle f = QuasiTransitive.walkDevice c ∧
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
      hp hqR hpp hμ Scycle Dcycle (ContainedAdmissible exh Dcycle) L hCycle
        (fun e _ => eventually_containedAdmissible exh Dcycle e) hcycle
        hcycleCard hne
  · apply gt_dlr_upper_of_active_star_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Sstar Dstar (ContainedAdmissible exh Dstar) Delta hStar
        (fun e _ => eventually_containedAdmissible exh Dstar e) hne
    intro n η e he
    exact data.exists_starCutset_of_active_geometric Φ hΦ hStar hstar hstarCard
      hinj η e he

/-- On a connected quasi-transitive graph, construct the separated actual
incidence-star and cycle families by automorphism packing, activate them by
finite-box containment, and obtain the `q < 1` DLR sandwich.  The bounded-
distance conclusions make the constructed selected families non-vacuous. -/
theorem lt_dlr_sandwich_of_quasiTransitive_contained
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    [Countable G.edgeSet]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp1.le)
    (hconn : G.Connected) (hqt : QuasiTransitive.IsQuasiTransitive G)
    {u₀ : V} {e₀ : G.edgeSet} (hu₀ : u₀ ∈ (e₀ : Sym2 V))
    (hr₀ : FK.EssentialEnhancement.OnDoubleRay e₀)
    {v₀ : V} (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle)
    (he₀ : (e₀ : Sym2 V) ∈ c₀.edges)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    ∃ (Delta L : ℕ) (Sstar Scycle : Set G.edgeSet)
      (Dstar Dcycle : G.edgeSet → Finset G.edgeSet),
      FKLimit.IsSeparatedDeviceFamily Sstar Dstar ∧
      FKLimit.IsSeparatedDeviceFamily Scycle Dcycle ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Sstar ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Scycle ∧
      (∀ f ∈ Sstar, (Dstar f).card ≤ Delta) ∧
      (∀ f ∈ Scycle, (Dcycle f).card ≤ L) ∧
      (∀ f ∈ Sstar, ∃ v : V,
        Dstar f = QuasiTransitive.starDevice G v ∧ v ∈ (f : Sym2 V)) ∧
      (∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
        c.length = L ∧ Dcycle f = QuasiTransitive.walkDevice c ∧
          (f : Sym2 V) ∈ c.edges) ∧
      let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
      let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
        (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
      FKLimit.StochasticallyDominates μ
        (FKLimit.bernoulliProduct
          (FKLimit.ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
      FKLimit.StochasticallyDominates
        (FKLimit.bernoulliProduct
          (FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  obtain ⟨Delta, Sstar, Dstar, _hdegree, hStar, hstarBounded, _hstarRay,
      hstarCard, hstar⟩ :=
    QuasiTransitive.exists_separated_star_devices G hconn hqt u₀ hu₀ hr₀
  obtain ⟨L, Scycle, Dcycle, _hL, hCycle, hcycleBounded, _hcycleRay,
      hcycleCard, hcycle⟩ :=
    QuasiTransitive.exists_separated_cycle_devices G hconn hqt c₀ hc₀ he₀ hr₀
  refine ⟨Delta, L, Sstar, Scycle, Dstar, Dcycle, hStar, hCycle,
    hstarBounded, hcycleBounded, hstarCard, hcycleCard, hstar, hcycle, ?_⟩
  exact lt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained
    exh data Φ hΦ hinj hq hp0 hp1 hq1 hμ Sstar Dstar Delta hStar hstar
      hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne

/-- The reverse-prime (`q > 1`) counterpart constructed by the same genuine
quasi-transitive star/cycle packing.  The lower product is enhanced on the
cycle family and the upper product is lowered on the incidence-star family. -/
theorem gt_dlr_sandwich_of_quasiTransitive_contained
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    [Countable G.edgeSet]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ DLRMeasures exh Φ (lt_trans zero_lt_one hq1 : 0 < q) hp1.le)
    (hconn : G.Connected) (hqt : QuasiTransitive.IsQuasiTransitive G)
    {u₀ : V} {e₀ : G.edgeSet} (hu₀ : u₀ ∈ (e₀ : Sym2 V))
    (hr₀ : FK.EssentialEnhancement.OnDoubleRay e₀)
    {v₀ : V} (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle)
    (he₀ : (e₀ : Sym2 V) ∈ c₀.edges)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    ∃ (Delta L : ℕ) (Sstar Scycle : Set G.edgeSet)
      (Dstar Dcycle : G.edgeSet → Finset G.edgeSet),
      FKLimit.IsSeparatedDeviceFamily Sstar Dstar ∧
      FKLimit.IsSeparatedDeviceFamily Scycle Dcycle ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Sstar ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Scycle ∧
      (∀ f ∈ Sstar, (Dstar f).card ≤ Delta) ∧
      (∀ f ∈ Scycle, (Dcycle f).card ≤ L) ∧
      (∀ f ∈ Sstar, ∃ v : V,
        Dstar f = QuasiTransitive.starDevice G v ∧ v ∈ (f : Sym2 V)) ∧
      (∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
        c.length = L ∧ Dcycle f = QuasiTransitive.walkDevice c ∧
          (f : Sym2 V) ∈ c.edges) ∧
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
  obtain ⟨Delta, Sstar, Dstar, _hdegree, hStar, hstarBounded, _hstarRay,
      hstarCard, hstar⟩ :=
    QuasiTransitive.exists_separated_star_devices G hconn hqt u₀ hu₀ hr₀
  obtain ⟨L, Scycle, Dcycle, _hL, hCycle, hcycleBounded, _hcycleRay,
      hcycleCard, hcycle⟩ :=
    QuasiTransitive.exists_separated_cycle_devices G hconn hqt c₀ hc₀ he₀ hr₀
  refine ⟨Delta, L, Sstar, Scycle, Dstar, Dcycle, hStar, hCycle,
    hstarBounded, hcycleBounded, hstarCard, hcycleCard, hstar, hcycle, ?_⟩
  exact gt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained
    exh data Φ hΦ hinj hp0 hp1 hq1 hμ Sstar Dstar Delta hStar hstar
      hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne

end
end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.eventually_containedAdmissible
#print axioms FK.EnhancedTransport.mem_activeEdges_containedAdmissible
#print axioms FK.EnhancedTransport.mem_activeEdges_containedAdmissible_of_isSeparated
#print axioms FK.EnhancedTransport.eventually_mem_activeEdges_containedAdmissible
#print axioms FK.EnhancedTransport.lt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained
#print axioms FK.EnhancedTransport.gt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained
#print axioms FK.EnhancedTransport.lt_dlr_sandwich_of_quasiTransitive_contained
#print axioms FK.EnhancedTransport.gt_dlr_sandwich_of_quasiTransitive_contained
