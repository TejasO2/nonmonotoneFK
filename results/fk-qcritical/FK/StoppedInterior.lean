import FK.FKSequentialCoupling
import FK.CanonicalFreeInterior
import FK.FiniteGraphTransport

/-!
# Free interior after an exposed exterior cylinder

This module joins the canonical sequential prefix filter to the actual
free-interior FK factorization.  The exposed exterior edges are enumerated
before every interior edge.  After sampling precisely this exterior history,
the lower continuation, decoded on the interior labelled edges, is the actual
free interior FK PMF.
-/

namespace FK.Exploration.StoppedInterior

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.Exploration.FKCoupling

/-- Filtering a PMF and transporting its state space by an equivalence
commute, provided the event is transported by the same equivalence. -/
theorem map_filter_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B)
    (μ : PMF A) (E : Set B)
    (hA : ∃ a ∈ e ⁻¹' E, a ∈ μ.support)
    (hB : ∃ b ∈ E, b ∈ (μ.map e).support) :
    (μ.filter (e ⁻¹' E) hA).map e = (μ.map e).filter E hB := by
  have hmap : ∀ b, (μ.map e) b = μ (e.symm b) := by
    intro b
    have h := map_apply_of_injective e.injective μ (e.symm b)
    simpa using h
  have hind : ∀ b, E.indicator (⇑(μ.map e)) b =
      (e ⁻¹' E).indicator (⇑μ) (e.symm b) := by
    intro b
    by_cases hb : b ∈ E
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (show e.symm b ∈ e ⁻¹' E from by simpa using hb), hmap]
    · have hab : e.symm b ∉ e ⁻¹' E := by simpa using hb
      rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hab]
  have hsum : (∑' a, (e ⁻¹' E).indicator (⇑μ) a) =
      ∑' b, E.indicator (⇑(μ.map e)) b := by
    rw [tsum_fintype, tsum_fintype]
    apply Fintype.sum_equiv e
    intro a
    rw [hind (e a), e.symm_apply_apply]
  apply PMF.ext
  intro b
  have hleft : ((μ.filter (e ⁻¹' E) hA).map e) b =
      (μ.filter (e ⁻¹' E) hA) (e.symm b) := by
    have h := map_apply_of_injective e.injective (μ.filter (e ⁻¹' E) hA) (e.symm b)
    simpa using h
  rw [hleft, PMF.filter_apply, PMF.filter_apply, hsum, ← hind b]

/-- The exterior-first enumeration of `Fin m ⊕ Fin k`. -/
def exteriorFirst {m k : ℕ} : Fin (k + m) ≃ Fin m ⊕ Fin k :=
  Equiv.trans (finSumFinEquiv (m := k) (n := m)).symm (Equiv.sumComm (Fin k) (Fin m))

/-- Transport the separated sum graph to its exterior-first finite edge
enumeration. -/
def transportedAmbient {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K) :
    LabelledMultigraph :=
  (ambientOfSum (splitSource si so) (splitTarget ti xo)).transport
    (Equiv.refl (U ⊕ K)) exteriorFirst

/-- Back to the actual sum-labelled configuration. -/
def toAmbientConfig {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K) :
    (transportedAmbient si ti so xo).Configuration ≃
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).Configuration :=
  (ambientOfSum (splitSource si so) (splitTarget ti xo)).transportConfig
    (Equiv.refl (U ⊕ K)) exteriorFirst

lemma toAmbientConfig_inr {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (y : Fin (k + m) → Bool) (i : Fin k) :
    toAmbientConfig si ti so xo y (Sum.inr i) = y (Fin.castAdd m i) := by
  change y (exteriorFirst.symm (Sum.inr i)) = y (Fin.castAdd m i)
  congr 1

/-- A history recording exactly the exterior coordinates first. -/
def exteriorHistory {m k : ℕ} (ρ : Fin m ⊕ Fin k → Bool) :
    List Bool :=
  List.ofFn (fun i : Fin k => ρ (Sum.inr i))

/-- The exterior prefix is exactly the exterior-configuration cylinder after
transport back to the actual sum-labelled graph. -/
lemma exteriorHistory_prefix_iff {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : (ambientOfSum (splitSource si so) (splitTarget ti xo)).Configuration)
    (y : Fin (k + m) → Bool) :
    exteriorHistory ρ <+: List.ofFn y ↔
      toAmbientConfig si ti so xo y ∈ exteriorFiber (exteriorConfig ρ) := by
  constructor
  · intro h
    simp only [exteriorFiber, Set.mem_setOf_eq, exteriorConfig, Function.comp_def]
    intro i
    have hi := h.getElem (i := i.1) (by simp [exteriorHistory])
    rw [toAmbientConfig_inr]
    simp only [exteriorHistory, List.getElem_ofFn] at hi
    convert hi.symm using 1
    · congr 1
    · rfl
  · intro h
    rw [List.prefix_iff_getElem]
    refine ⟨by simp only [exteriorHistory, List.length_ofFn]; omega, ?_⟩
    intro i hi
    have hik : i < k := by simpa [exteriorHistory] using hi
    have h' : (toAmbientConfig si ti so xo y) (Sum.inr (⟨i, hik⟩ : Fin k)) =
        ρ (Sum.inr (⟨i, hik⟩ : Fin k)) := h ⟨i, hik⟩
    simpa [exteriorHistory, toAmbientConfig_inr] using h'.symm

/-- Exact free-interior law after exposing the exterior history. -/
theorem extendLower_exteriorHistory_eq_free {U K : Type*} [Fintype U] [Fintype K]
    {m k : ℕ} (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ρ : Fin m ⊕ Fin k → Bool)
    (hsep : Separated si ti so xo (exteriorConfig ρ)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let μ := T.fkPMF hq hp₁.le T.freeBoundary
    (extendLower (canonicalNext μ (FK.Exploration.FKCoupling.fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary))
      (exteriorHistory ρ) m).map (fun y =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let T := transportedAmbient si ti so xo
  let e : (Fin (k + m) → Bool) ≃ (Fin m ⊕ Fin k → Bool) :=
    toAmbientConfig si ti so xo
  let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le T.freeBoundary
  have hμ := FK.Exploration.FKCoupling.fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary
  have hlen : (exteriorHistory ρ).length + m = k + m := by
    simp [exteriorHistory]
  dsimp only
  rw [extendLower_canonicalNext μ hμ (exteriorHistory ρ) m hlen]
  let P := prefixCylinder (n := k + m) (exteriorHistory ρ)
  have hP : P = e ⁻¹' exteriorFiber (exteriorConfig ρ) := by
    ext y
    exact exteriorHistory_prefix_iff si ti so xo ρ y
  have htransport : μ.map e = G.fkPMF hq hp₁.le G.freeBoundary := by
    exact G.map_transport_fkPMF_free (Equiv.refl (U ⊕ K)) exteriorFirst hq hp₀ hp₁
  have hB : ∃ a ∈ exteriorFiber (exteriorConfig ρ), a ∈ (μ.map e).support := by
    rw [htransport]
    exact exteriorFiber_support_actual _ _ hq hp₀ hp₁ (exteriorConfig ρ)
  have hfilter : (μ.filter P
      (prefixCylinder_support_of_positive μ hμ (exteriorHistory ρ) (by omega))).map e =
      (G.fkPMF hq hp₁.le G.freeBoundary).filter (exteriorFiber (exteriorConfig ρ))
        (exteriorFiber_support_actual _ _ hq hp₀ hp₁ (exteriorConfig ρ)) := by
    simp only [hP]
    have hA : ∃ a ∈ e ⁻¹' exteriorFiber (exteriorConfig ρ), a ∈ μ.support := by
      rw [← hP]
      exact prefixCylinder_support_of_positive μ hμ (exteriorHistory ρ) (by omega)
    have h0 := map_filter_equiv e μ (exteriorFiber (exteriorConfig ρ)) hA hB
    simp only [htransport] at h0
    with_unfolding_all exact h0
  rw [PMF.map_comp]
  have hc : (fun y => interiorConfig ((toAmbientConfig si ti so xo) (toConfig (k + m) y))) ∘
      List.ofFn =
      interiorConfig ∘ e := by
    funext ω
    change interiorConfig (e (toConfig (k + m) (List.ofFn ω))) = interiorConfig (e ω)
    rw [toConfig_ofFn]
  rw [hc, ← PMF.map_comp, hfilter]
  rw [← filter_ambient_fkPMF_eq_map_glue_region_free si ti so xo hq hp₀ hp₁
    (exteriorConfig ρ) hsep]
  refine (PMF.map_comp _ _ _).trans ?_
  have hid : (interiorConfig (I := Fin m) (O := Fin k)) ∘
      (fun (ω : Fin m → Bool) => glue (I := Fin m) (O := Fin k) ω (exteriorConfig ρ)) = id := by
    funext ω
    rfl
  rw [hid]
  with_unfolding_all exact PMF.map_id _

/-- Separation needed for the lower interior follows from a canonical
outer-region stratum of any pointwise-larger upper configuration. -/
lemma separated_of_le_of_outerRegion {U K : Type*} [Fintype U] [Fintype K]
    {m k : ℕ} (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ π : Fin m ⊕ Fin k → Bool) (hπρ : π ≤ ρ)
    (hright : ExteriorHasRight so xo)
    (hR : (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr) :
    Separated si ti so xo (exteriorConfig π) := by
  have hupper := separated_of_outerRegion_eq_right si ti so xo ρ hright hR
  intro o ho
  apply hupper o
  have hle := hπρ (Sum.inr o)
  rw [Bool.le_iff_imp] at hle
  exact hle ho

/-- Exact free lower interior after exposing an exterior history below an
upper canonical outer-region stratum. -/
theorem extendLower_exteriorHistory_eq_free_of_le_outerRegion
    {U K : Type*} [Fintype U] [Fintype K]
    {m k : ℕ} (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ρ π : Fin m ⊕ Fin k → Bool) (hπρ : π ≤ ρ)
    (hright : ExteriorHasRight so xo)
    (hR : (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let μ := T.fkPMF hq hp₁.le T.freeBoundary
    (extendLower (canonicalNext μ (FK.Exploration.FKCoupling.fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary))
      (exteriorHistory π) m).map (fun y =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  apply extendLower_exteriorHistory_eq_free si ti so xo hq hp₀ hp₁ π
  exact separated_of_le_of_outerRegion si ti so xo ρ π hπρ hright hR

/-- Complete an exposed exterior history by closing every interior edge. -/
def ambientOfHistory {m k : ℕ} (x : List Bool) : Fin m ⊕ Fin k → Bool :=
  Sum.elim (fun _ : Fin m => false) (toConfig k x)

lemma exteriorHistory_ambientOfHistory {m k : ℕ} {x : List Bool}
    (hx : x.length = k) : exteriorHistory (m := m) (k := k) (ambientOfHistory (m := m) (k := k) x) = x := by
  apply List.ext_getElem
  · simp [exteriorHistory, hx]
  · intro i h₁ h₂
    simp only [exteriorHistory, List.getElem_ofFn, ambientOfHistory, Sum.elim_inr, toConfig]
    exact List.getD_eq_getElem _ _ (by simpa [hx] using h₂)

/-- Normalized lower interior law after filtering the complete exterior prefix
on an upper outer-region stratum.  Positivity `hU` is only the support witness
required by finite conditioning; no Markov/free-law clause is assumed. -/
theorem normalized_upperStratum_interior {U K : Type*} [Fintype U] [Fintype K]
    {m k : ℕ} (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ρ : Fin m ⊕ Fin k → Bool) (hright : ExteriorHasRight so xo)
    (hR : (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr) :
    let T := transportedAmbient si ti so xo
    let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le T.freeBoundary
    let r := FK.Exploration.FKCoupling.upperRateNN q p
    let hbound : ∀ x, (canonicalNext μ
      (FK.Exploration.FKCoupling.fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary) x true).toReal ≤
        (r : ℝ) := fun x => FK.Exploration.FKCoupling.fk_upper_nextBound
          _ _ T.freeBoundary hq hp₀ hp₁ x
    let pfx := extendPair (orderedUpperStep μ
      (FK.Exploration.FKCoupling.fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary) r
      (FK.Exploration.FKCoupling.upperRateNN_le_one hq hp₁.le) hbound) [] [] k
    ∀ hU : ∃ z ∈ {z : List Bool × List Bool | z.2 = exteriorHistory ρ}, z ∈ pfx.support,
      (pfx.filter {z : List Bool × List Bool | z.2 = exteriorHistory ρ} hU).bind
        (fun z => (extendPair (orderedUpperStep μ
          (FK.Exploration.FKCoupling.fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary) r
          (FK.Exploration.FKCoupling.upperRateNN_le_one hq hp₁.le) hbound)
          z.1 z.2 m).map (fun y =>
            interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y.1)))) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  intro T μ r hbound pfx hU
  apply bind_eq_self_of_forall_support _ _ _ (fun z hz => ?_)
  rw [PMF.mem_support_filter_iff] at hz
  obtain ⟨hzU, hz⟩ := hz
  have hzU : z.2 = exteriorHistory ρ := hzU
  have hμ := FK.Exploration.FKCoupling.fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary
  let step := orderedUpperStep μ hμ r
    (FK.Exploration.FKCoupling.upperRateNN_le_one hq hp₁.le) hbound
  have hfst : ∀ x y, (step x y).map Prod.fst = canonicalNext μ hμ x := by
    intro x y
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (FK.Exploration.FKCoupling.upperRateNN_le_one hq hp₁.le) (hbound x)).map_fst
  have hordstep : ∀ x y z, z ∈ (step x y).support → z.1 ≤ z.2 := by
    intro x y w hw
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (FK.Exploration.FKCoupling.upperRateNN_le_one hq hp₁.le) (hbound x)).ordered w hw
  have hlen := extendPair_length_support step [] [] k hz
  have hord := extendPair_ordered step hordstep List.Forall₂.nil k hz
  have hex : exteriorHistory (m := m) (ambientOfHistory z.1) = z.1 :=
    exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.1)
  have hconf : toConfig k z.1 ≤ exteriorConfig ρ := by
    have hc := toConfig_le_of_forall₂ (n := k) hord
    rw [hzU] at hc
    simpa only [exteriorHistory, toConfig_ofFn, exteriorConfig, Function.comp_def] using hc
  have hmono : ambientOfHistory z.1 ≤ ρ := by
    intro a
    cases a with
    | inl a => exact Bool.false_le _
    | inr a => exact hconf a
  calc
    (extendPair step z.1 z.2 m).map (fun y =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y.1))) =
        ((extendPair step z.1 z.2 m).map Prod.fst).map (fun y =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) := by
      rw [PMF.map_comp]
      rfl
    _ = (extendLower (canonicalNext μ hμ) z.1 m).map (fun y =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) := by
      rw [extendPair_map_fst step (canonicalNext μ hμ) hfst]
    _ = (extendLower (canonicalNext μ hμ) (exteriorHistory (m := m) (ambientOfHistory z.1)) m).map
          (fun y => interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) := by
      rw [hex]
    _ = _ := by
      apply extendLower_exteriorHistory_eq_free_of_le_outerRegion si ti so xo hq hp₀ hp₁
        ρ (ambientOfHistory z.1) hmono hright hR

end FK.Exploration.StoppedInterior
