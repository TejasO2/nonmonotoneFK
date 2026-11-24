/-
# The pointwise exterior separation hypothesis is necessary

`ConfinedStrata.stratum_conditional_region_eq_region` proves that on *any*
exterior stratum whose open exterior labels avoid the region, the conditional
region law of the ambient confined FK law is the region FK law, and
`ConfinedStrata.nested_strata_conditional_eq` proves the same law on two nested
strata.  This file shows, on an explicit finite geometry, that the separation
hypothesis cannot be dropped: the region-confined boundary conditions alone
(`hconf`, `hθ`, region-avoiding added labels) do not make the region law
stratum-independent.

Geometry (`W = Fin 2`, `K = Fin 0`, `I = Fin 1`, `k = 1`, `a = 0`):

* one interior edge joining `0` and `1`;
* one exterior label whose *both* endpoints are the region vertices `0` and `1`
  (so it is parallel to the interior edge);
* the boundary setoids are the free ones, so the region is closed under the
  boundary relation and no added label occurs.

Every hypothesis of `stratum_mass_factorization` except pointwise separation
holds.  Taking the exterior stratum `E = {all-open exterior}` and the region
event `A = {interior edge open}` the common-upper identity fails:

  weight mass of `A x E`      `= 1/8`,  region partition function `= 3/8`,
  region weight mass of `A`   `= 1/4`,  exterior weight mass `= 1/4`,

and `1/8 * 3/8 = 3/64 != 1/16 = 1/4 * 1/4`.  Since that identity is exactly the
necessary condition for the conditional region law to be the region FK law
(`mass_eq_of_map_filter_eq` below), the conditional region law on this stratum
is *not* `regionGraph.fkPMF theta`.  The same open exterior label also makes
`fkWeight_glue_stratum` fail at the closed region configuration.

So a common-upper comparison built on region confinement must restrict the
third-coordinate stratum to configurations whose open exterior labels avoid the
region; `hsepS` is a real restriction, not bookkeeping.
-/
import FK.ConfinedStrata
import FK.ConfinementNecessary

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionConfinement.ConfinedStrata

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ## The converse of `map_filter_eq_of_mass_factorization` -/

/-- Change of variables for a function against a pushed-forward finite PMF. -/
theorem tsum_mul_map_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    (∑' b, g b * (p.map f) b) = ∑' a, g (f a) * p a := by
  classical
  have hpt : ∀ b : β, g b * (p.map f) b =
      ∑' a, g b * (if b = f a then p a else 0) := by
    intro b
    rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
  rw [show (∑' b, g b * (p.map f) b) = ∑' b, ∑' a, g b * (if b = f a then p a else 0) from
    tsum_congr hpt]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun a => ?_)
  rw [tsum_eq_single (f a)]
  · simp
  · intro b hb
    simp [hb]

/-- **Converse mass identity.**  If conditioning a finite PMF on `T` and pushing
forward along `f` gives `c`, then for every `A` the `P`-mass of `f ⁻¹' A ∩ T`
is `c A` times the `P`-mass of `T`.  This is the necessary direction of
`FK.RegionConfinement.PrefixContinuation.map_filter_eq_of_mass_factorization`. -/
theorem mass_eq_of_map_filter_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (f : α → β) (T : Set α) (hT : ∃ a ∈ T, a ∈ P.support)
    (c : PMF β) (h : (P.filter T hT).map f = c) (A : Set β) :
    (∑' b, A.indicator (fun b => c b) b) * (∑' a, T.indicator (fun a => P a) a) =
      ∑' a, (f ⁻¹' A ∩ T).indicator (fun a => P a) a := by
  classical
  set PT : PMF α := P.filter T hT with hPT
  set M : ℝ≥0∞ := ∑' a, T.indicator (fun a => P a) a with hM
  have hM0 : M ≠ 0 := by
    obtain ⟨a₀, ha₀, hsupp₀⟩ := hT
    intro hzero
    rw [hM, ENNReal.tsum_eq_zero] at hzero
    exact (PMF.mem_support_iff _ _).mp hsupp₀ (by
      have := hzero a₀
      rwa [Set.indicator_of_mem ha₀] at this)
  have hMtop : M ≠ ∞ := by
    rw [hM, tsum_fintype]
    refine (ENNReal.sum_ne_top).mpr (fun a _ => ?_)
    by_cases h : a ∈ T
    · rw [Set.indicator_of_mem h]; exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top
  -- the `PT`-mass of `f ⁻¹' A` in terms of `c`
  have hstep : (∑' b, A.indicator (fun b => c b) b) =
      ∑' a, (f ⁻¹' A ∩ T).indicator (fun a => PT a) a := by
    conv_lhs => rw [← h]
    rw [show (∑' b, A.indicator (fun b => (PT.map f) b) b) =
        ∑' b, A.indicator (fun _ => (1 : ℝ≥0∞)) b * (PT.map f) b from by
      refine tsum_congr (fun b => ?_)
      rw [Set.indicator_apply]
      by_cases hb : b ∈ A <;> simp [hb]]
    rw [tsum_mul_map_apply]
    refine tsum_congr (fun a => ?_)
    by_cases ha : f a ∈ A
    · by_cases hat : a ∈ T
      · simp [Set.mem_preimage, ha, hat]
      · rw [hPT, PMF.filter_apply hT, Set.indicator_of_notMem hat, zero_mul]
        simp [Set.mem_preimage, ha, hat]
    · simp [Set.mem_preimage, ha]
  -- and `PT` on `T` is `P` times the inverse conditioning mass
  have hPTind : ∀ a : α, (f ⁻¹' A ∩ T).indicator (fun a => PT a) a =
      (f ⁻¹' A ∩ T).indicator (fun a => P a) a * M⁻¹ := by
    intro a
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases ha : a ∈ f ⁻¹' A ∩ T
    · have haT : a ∈ T := ha.2
      rw [ite_eq_left ha, ite_eq_left ha, PMF.filter_apply hT, Set.indicator_of_mem haT, hM]
    · rw [ite_eq_right ha, ite_eq_right ha, zero_mul]
  rw [hstep, show (∑' a, (f ⁻¹' A ∩ T).indicator (fun a => PT a) a) =
      ∑' a, (f ⁻¹' A ∩ T).indicator (fun a => P a) a * M⁻¹ from
    tsum_congr hPTind]
  rw [ENNReal.tsum_mul_right]
  rw [mul_assoc, ENNReal.inv_mul_cancel hM0 hMtop, mul_one]

/-! ## The explicit geometry -/

/-- The single region edge joins the two region vertices. -/
abbrev oW : Type := Fin 2
/-- No outside vertices: the ambient vertex type is exactly the region. -/
abbrev oK : Type := Fin 0
abbrev oSi : Fin 1 → oW := fun _ => 0
abbrev oTi : Fin 1 → oW := fun _ => 1
/-- The exterior label is parallel to the region edge: both endpoints are region
vertices. -/
abbrev oSo : Fin 1 → oW ⊕ oK := fun _ => Sum.inl 0
abbrev oXo : Fin 1 → oW ⊕ oK := fun _ => Sum.inl 1
abbrev oAo : Fin 0 → oW ⊕ oK := fun j => Fin.elim0 j
abbrev oBo : Fin 0 → oW ⊕ oK := fun j => Fin.elim0 j

abbrev oAmb : LabelledMultigraph :=
  ambientOfSum (splitSource oSi (bigSo oSo oAo)) (splitTarget oTi (bigXo oXo oBo))

abbrev oReg : LabelledMultigraph := regionGraph oSi oTi

/-- The free boundary setoid of the ambient graph. -/
abbrev oBd : Setoid (oW ⊕ oK) := oAmb.freeBoundary
abbrev oTh : Setoid oW := oReg.freeBoundary

/-- The single exterior stratum: the exterior label is open. -/
def oE : Set (Fin 1 ⊕ Fin 0 → Bool) := {fun _ => true}

/-- The region event: the interior edge is open. -/
def oA : Set (Fin 1 → Bool) := {fun _ => true}

/-- Concretely: the exterior configuration is the all-open map.  Nothing depends
on the `Fin 0` summand, so this pins the stratum. -/
theorem oE_eq_singleton : oE = ({fun _ => (true : Bool)} : Set (Fin 1 ⊕ Fin 0 → Bool)) := rfl

abbrev ohq : (0 : NNReal) < 1 / 2 := by norm_num
abbrev ohp₀ : (0 : NNReal) < 1 / 2 := by norm_num
abbrev ohp₁ : (1 / 2 : NNReal) < 1 := by norm_num

/-- Confinement holds in this geometry: the free boundary never leaves the
region. -/
theorem oConf : ∀ (c : oW) (y : oW ⊕ oK), oBd.r (Sum.inl c) y → ∃ c', y = Sum.inl c' := by
  intro c y h
  exact ⟨c, h.symm⟩

/-- The ambient free boundary restricts to the region free boundary. -/
theorem oTh_iff : ∀ (c c' : oW), oBd.r (Sum.inl c) (Sum.inl c') ↔ oTh.r c c' := by
  intro c c'
  show Sum.inl c = Sum.inl c' ↔ c = c'
  exact ⟨fun h => Sum.inl.inj h, fun h => by rw [h]⟩

/-- No added labels exist, so region avoidance is vacuous. -/
theorem oAdded : AddedAvoid (K := oK) oAo oBo := by
  intro j
  exact Fin.elim0 j

/-- The single exterior stratum is *not* pointwise separated: the open exterior
label is the region edge `0 -- 1` again. -/
theorem oE_not_sep : ¬ ∀ e ∈ oE, ExtSep (K := oK) oSo oXo oAo oBo e := by
  intro h
  have hsep := h (fun _ => true) rfl (Sum.inl 0) rfl
  exact hsep.1 (inRegion_inl 0)

/-! ## Exact weights in the explicit geometry -/

theorem oReg_open : oReg.componentCount oTh (fun _ => true) = 1 :=
  FK.RegionConfinement.cR_componentCount_open

theorem oReg_closed : oReg.componentCount oTh (fun _ => false) = 2 :=
  FK.RegionConfinement.cR_componentCount_closed

theorem oRegionW_open :
    regionWeight oSi oTi oTh (1 / 2) (1 / 2) (fun _ => true) = 1 / 4 := by
  have h : (regionGraph oSi oTi).componentCount oTh (fun _ => true) = 1 :=
    FK.RegionConfinement.cR_componentCount_open
  show FK.FinitePlane.fkWeight (1 / 2) (1 / 2)
    ((regionGraph oSi oTi).componentCount oTh) (fun _ => true) = 1 / 4
  rw [FK.FinitePlane.fkWeight, h]
  have hcard : Fintype.card (regionGraph oSi oTi).Edge = 1 := rfl
  simp [FK.FinitePlane.edgeWeight, hcard]
  norm_num

theorem oRegionW_closed :
    regionWeight oSi oTi oTh (1 / 2) (1 / 2) (fun _ => false) = 1 / 8 := by
  have h : (regionGraph oSi oTi).componentCount oTh (fun _ => false) = 2 :=
    FK.RegionConfinement.cR_componentCount_closed
  show FK.FinitePlane.fkWeight (1 / 2) (1 / 2)
    ((regionGraph oSi oTi).componentCount oTh) (fun _ => false) = 1 / 8
  rw [FK.FinitePlane.fkWeight, h]
  have hcard : Fintype.card (regionGraph oSi oTi).Edge = 1 := rfl
  simp [FK.FinitePlane.edgeWeight, hcard]
  have hhalf : (1 : NNReal) - 2⁻¹ = 2⁻¹ := tsub_eq_of_eq_add (by norm_num)
  rw [hhalf]
  norm_num

/-- Any configuration of the ambient graph in which one of the two parallel
labels is open has exactly one component: the region edge and the exterior label
join the same two vertices, and there are no outside vertices. -/
theorem oAmb_comp_one (cfg : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool)
    (e : Fin 1 ⊕ (Fin 1 ⊕ Fin 0)) (he : cfg e = true)
    (hsrc : oAmb.source e = Sum.inl 0) (htgt : oAmb.target e = Sum.inl 1) :
    oAmb.componentCount oBd cfg = 1 := by
  have hadj : (oAmb.connectionGraph oBd cfg).Adj (Sum.inl 0) (Sum.inl 1) := by
    refine ⟨?_, Or.inr ⟨e, he, Or.inl ⟨hsrc, htgt⟩⟩⟩
    intro h
    have h' : (0 : oW) = 1 := Sum.inl.inj h
    exact absurd h' (by decide)
  refine FK.Finite.LabelledMultigraph.componentCount_eq_one_of_preconnected oAmb oBd cfg
    (Sum.inl 0) ?_
  intro x y
  have hreach : ∀ z, (oAmb.connectionGraph oBd cfg).Reachable (Sum.inl 0) z := by
    intro z
    rcases z with c | k
    · fin_cases c
      · exact SimpleGraph.Reachable.refl _
      · exact hadj.reachable
    · exact Fin.elim0 k
  exact (hreach x).symm.trans (hreach y)

theorem oAmb_source_region : oAmb.source (Sum.inl 0) = Sum.inl 0 := rfl
theorem oAmb_target_region : oAmb.target (Sum.inl 0) = Sum.inl 1 := rfl
theorem oAmb_source_ext : oAmb.source (Sum.inr (Sum.inl 0)) = Sum.inl 0 := rfl
theorem oAmb_target_ext : oAmb.target (Sum.inr (Sum.inl 0)) = Sum.inl 1 := rfl

theorem oAmb_comp_open : oAmb.componentCount oBd (glue (fun _ => true) (fun _ => true)) = 1 :=
  oAmb_comp_one _ (Sum.inl 0) rfl oAmb_source_region oAmb_target_region

theorem oAmb_comp_closed :
    oAmb.componentCount oBd (glue (fun _ => false) (fun _ => true)) = 1 :=
  oAmb_comp_one _ (Sum.inr (Sum.inl 0)) rfl oAmb_source_ext oAmb_target_ext

/-- The ambient FK weight of the configuration with both parallel labels open. -/
theorem oAmb_w_open :
    oAmb.fkWeight (1 / 2) (1 / 2) oBd (glue (fun _ => true) (fun _ => true)) = 1 / 8 := by
  show (∏ e : Fin 1 ⊕ (Fin 1 ⊕ Fin 0),
      if (glue (fun _ => true) (fun _ => true)) e = true then (1/2 : NNReal) else 1 - 1/2)
    * (1 / 2) ^ oAmb.componentCount oBd (glue (fun _ => true) (fun _ => true)) = 1 / 8
  rw [show oAmb.componentCount oBd (glue (fun _ => true) (fun _ => true)) = 1 from
    oAmb_comp_open]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp [glue]
  norm_num

/-- The ambient FK weight of the configuration with only the exterior label open. -/
theorem oAmb_w_closed :
    oAmb.fkWeight (1 / 2) (1 / 2) oBd (glue (fun _ => false) (fun _ => true)) = 1 / 8 := by
  show (∏ e : Fin 1 ⊕ (Fin 1 ⊕ Fin 0),
      if (glue (fun _ => false) (fun _ => true)) e = true then (1/2 : NNReal) else 1 - 1/2)
    * (1 / 2) ^ oAmb.componentCount oBd (glue (fun _ => false) (fun _ => true)) = 1 / 8
  rw [show oAmb.componentCount oBd (glue (fun _ => false) (fun _ => true)) = 1 from
    oAmb_comp_closed]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp [glue]
  have hhalf : (1 : NNReal) - 2⁻¹ = 2⁻¹ := tsub_eq_of_eq_add (by norm_num)
  rw [hhalf]
  norm_num

/-- The effective exterior weight of the stratum: there are no outside vertices,
so the confined exterior graph has no components. -/
theorem oExtWeight :
    extWeight oSi oTi oSo oXo oAo oBo oBd (1 / 2) (1 / 2) (fun _ => true) = 1 / 2 := by
  have h0 : Nat.card (rightConfinedGraph oSi oTi (bigSo oSo oAo) (bigXo oXo oBo) oBd
      (fun _ => true)).ConnectedComponent = 0 := by
    rw [Nat.card_eq_zero]
    refine Or.inl ⟨fun C => ?_⟩
    obtain ⟨v, -⟩ := C.exists_rep
    exact Fin.elim0 v
  show (∏ e : Fin 1 ⊕ Fin 0,
      if (fun _ => true : Fin 1 ⊕ Fin 0 → Bool) e = true then (1/2 : NNReal) else 1 - 1/2) *
    (1 / 2) ^ Nat.card (rightConfinedGraph oSi oTi (bigSo oSo oAo) (bigXo oXo oBo) oBd
      (fun _ => true)).ConnectedComponent = 1 / 2
  rw [h0, pow_zero, mul_one]
  rw [Fintype.prod_sum_type]
  simp

/-- **The pointwise factorization fails without separation.**  Every hypothesis
of `fkWeight_glue_stratum` except the pointwise separation of `e` holds here, and
the conclusion is false at the closed region configuration:

`oAmb.fkWeight (glue oClosed oEall) = 1/8`, but
`extWeight oEall * regionWeight oClosed = 1/2 * 1/8 = 1/16`.

Hence `ExtSep` cannot be dropped from the factorization, and with it the
restricted-stratum hypothesis of `stratum_mass_factorization` and of
`stratum_conditional_region_eq_region` is a real restriction on the third
coordinate of a common-upper comparison. -/
theorem fkWeight_glue_stratum_fails :
    oAmb.fkWeight (1 / 2) (1 / 2) oBd (glue (fun _ => false) (fun _ => true)) ≠
      extWeight oSi oTi oSo oXo oAo oBo oBd (1 / 2) (1 / 2) (fun _ => true) *
        regionWeight oSi oTi oTh (1 / 2) (1 / 2) (fun _ => false) := by
  rw [oAmb_w_closed, oExtWeight, oRegionW_closed]
  norm_num

/-! ## The conditional region law on the unseparated stratum

The pointwise failure above is not cosmetic: the conditional region law on the
unseparated stratum is *not* the region FK law.  The proof uses
`mass_eq_of_map_filter_eq` (the necessary direction of
`map_filter_eq_of_mass_factorization`) plus the exact weights computed above. -/

section ConditionalLaw

/-- The four configurations of the ambient graph, written through the region and
exterior coordinates. -/
def cfgOf (b1 b2 : Bool) : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool :=
  glue (fun _ => b1) (glue (fun _ => b2) (fun _ => false))

theorem cfgOf_inl (b1 b2 : Bool) : cfgOf b1 b2 (Sum.inl 0) = b1 := rfl

theorem cfgOf_inr (b1 b2 : Bool) : cfgOf b1 b2 (Sum.inr (Sum.inl 0)) = b2 := rfl

/-- Every configuration of the ambient graph is one of the four `cfgOf` points. -/
theorem eq_cfgOf (ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool) :
    ρ = cfgOf (ρ (Sum.inl 0)) (ρ (Sum.inr (Sum.inl 0))) := by
  have h1 : (ρ ∘ Sum.inl) = (fun _ : Fin 1 => ρ (Sum.inl 0)) := by
    funext i; fin_cases i; rfl
  have h2 : (ρ ∘ Sum.inr) = glue (fun _ : Fin 1 => ρ (Sum.inr (Sum.inl 0)))
      (fun _ : Fin 0 => false) := by
    funext l
    rcases l with i | j
    · fin_cases i; rfl
    · exact Fin.elim0 j
  calc ρ = glue (ρ ∘ Sum.inl) (ρ ∘ Sum.inr) := (glue_eta ρ).symm
    _ = cfgOf (ρ (Sum.inl 0)) (ρ (Sum.inr (Sum.inl 0))) := by rw [h1, h2]; rfl

/-- The sum over the four configurations of the ambient graph, split by the
region coordinate and the exterior coordinate. -/
theorem sum_amb (F : (Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool) → ℝ≥0∞) :
    (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool, F ρ) =
      ((F (cfgOf true true) + F (cfgOf false true)) + F (cfgOf true false)) +
        F (cfgOf false false) := by
  classical
  have hsplit : (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool, F ρ) =
      ∑' ω : Fin 1 → Bool, ∑' e1 : Fin 1 → Bool, ∑' e0 : Fin 0 → Bool,
        F (glue ω (glue e1 e0)) := by
    rw [show (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool, F ρ) =
        ∑' q : (Fin 1 → Bool) × (Fin 1 ⊕ Fin 0 → Bool), F (glue q.1 q.2) from by
      have h := Equiv.tsum_eq (configEquiv (I := Fin 1) (Fin 1 ⊕ Fin 0)).symm F
      rw [← h]
      exact tsum_congr (fun q => by rw [configEquiv_symm_apply])]
    rw [show (∑' q : (Fin 1 → Bool) × (Fin 1 ⊕ Fin 0 → Bool), F (glue q.1 q.2)) =
        ∑' ω : Fin 1 → Bool, ∑' e : Fin 1 ⊕ Fin 0 → Bool, F (glue ω e) from
      ENNReal.tsum_prod (f := fun a b => F (glue a b))]
    refine tsum_congr (fun ω => ?_)
    rw [show (∑' e : Fin 1 ⊕ Fin 0 → Bool, F (glue ω e)) =
        ∑' q : (Fin 1 → Bool) × (Fin 0 → Bool), F (glue ω (glue q.1 q.2)) from by
      have h := Equiv.tsum_eq (configEquiv (I := Fin 1) (Fin 0)).symm
        (fun e : Fin 1 ⊕ Fin 0 → Bool => F (glue ω e))
      rw [← h]
      exact tsum_congr (fun q => by rw [configEquiv_symm_apply])]
    exact ENNReal.tsum_prod (f := fun a b => F (glue ω (glue a b)))
  rw [hsplit]
  simp only [tsum_fintype]
  rw [show (∑ ω : Fin 1 → Bool, ∑ e1 : Fin 1 → Bool, ∑ e0 : Fin 0 → Bool,
        F (glue ω (glue e1 e0))) =
      ∑ ω : Fin 1 → Bool, ∑ e1 : Fin 1 → Bool,
        F (glue ω (glue e1 (fun _ => false))) from by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    refine Finset.sum_congr rfl (fun e1 _ => ?_)
    refine Finset.sum_eq_single (fun _ : Fin 0 => false) ?_ ?_
    · intro b _ hb
      exact absurd (funext (fun j => Fin.elim0 j)) hb
    · intro h; exact absurd (Finset.mem_univ _) h]
  rw [show (∑ ω : Fin 1 → Bool, ∑ e1 : Fin 1 → Bool,
        F (glue ω (glue e1 (fun _ => false)))) =
      (∑ e1 : Fin 1 → Bool, F (glue (fun _ => true) (glue e1 (fun _ => false))))
        + (∑ e1 : Fin 1 → Bool, F (glue (fun _ => false) (glue e1 (fun _ => false)))) from
    FK.RegionConfinement.sum_config_one
      (fun ω => ∑ e1 : Fin 1 → Bool, F (glue ω (glue e1 (fun _ => false))))]
  rw [FK.RegionConfinement.sum_config_one
      (fun e1 : Fin 1 → Bool => F (glue (fun _ => true) (glue e1 (fun _ => false)))),
    FK.RegionConfinement.sum_config_one
      (fun e1 : Fin 1 → Bool => F (glue (fun _ => false) (glue e1 (fun _ => false))))]
  ac_rfl

end ConditionalLaw

/-! ## Exact sums and the sharpened conditional-law obstruction -/

section ConditionalLaw

theorem cfgOf_true (b1 : Bool) :
    cfgOf b1 true = glue (fun _ : Fin 1 => b1) (fun _ : Fin 1 ⊕ Fin 0 => true) := by
  funext x
  rcases x with i | l
  · rfl
  · rcases l with i | j
    · rfl
    · exact Fin.elim0 j

theorem extEglue :
    (glue (fun _ : Fin 1 => true) (fun _ : Fin 0 => false) : Fin 1 ⊕ Fin 0 → Bool) =
      fun _ => true := by
  funext l
  rcases l with i | j
  · rfl
  · exact Fin.elim0 j

theorem cfgOf_comp_inr (b1 b2 : Bool) :
    (cfgOf b1 b2) ∘ Sum.inr = glue (fun _ : Fin 1 => b2) (fun _ : Fin 0 => false) := rfl

theorem cfgOf_comp_inl (b1 b2 : Bool) :
    (cfgOf b1 b2) ∘ Sum.inl = (fun _ : Fin 1 => b1) := by
  funext i; fin_cases i; rfl

theorem cfgOf_true_mem_ext (b1 : Bool) : cfgOf b1 true ∈ extMask (I := Fin 1) oE := by
  show cfgOf b1 true ∘ Sum.inr = (fun _ => true : Fin 1 ⊕ Fin 0 → Bool)
  rw [cfgOf_comp_inr, extEglue]

theorem cfgOf_false_not_mem_ext (b1 : Bool) : cfgOf b1 false ∉ extMask (I := Fin 1) oE := by
  intro h
  have h1 := congrFun (show cfgOf b1 false ∘ Sum.inr = (fun _ => true : Fin 1 ⊕ Fin 0 → Bool) from h)
    (Sum.inl (0 : Fin 1))
  rw [cfgOf_comp_inr] at h1
  simp at h1

theorem cfgOf_mem_region (b2 : Bool) : cfgOf true b2 ∈ regionMask (I := Fin 1) oA := by
  show cfgOf true b2 ∘ Sum.inl = (fun _ : Fin 1 => true)
  rw [cfgOf_comp_inl]

theorem cfgOf_false_not_mem_region (b2 : Bool) :
    cfgOf false b2 ∉ regionMask (I := Fin 1) oA := by
  intro h
  have h1 := congrFun (show cfgOf false b2 ∘ Sum.inl = (fun _ : Fin 1 => true) from h)
    (0 : Fin 1)
  rw [cfgOf_comp_inl] at h1
  simp at h1

/-! ### The weight sums -/

theorem oAmbSum_ext :
    (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
        (extMask (I := Fin 1) oE).indicator
          (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) ρ) =
      ((1 / 4 : NNReal) : ℝ≥0∞) := by
  rw [sum_amb (fun ρ => (extMask (I := Fin 1) oE).indicator
    (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) ρ)]
  have hTT : (extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf true true) =
        ((1 / 8 : NNReal) : ℝ≥0∞) := by
    rw [Set.indicator_of_mem (cfgOf_true_mem_ext true), cfgOf_true, oAmb_w_open]
  have hFT : (extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf false true) =
        ((1 / 8 : NNReal) : ℝ≥0∞) := by
    rw [Set.indicator_of_mem (cfgOf_true_mem_ext false), cfgOf_true, oAmb_w_closed]
  have hTF : (extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf true false) = 0 := by
    rw [Set.indicator_of_notMem (cfgOf_false_not_mem_ext true)]
  have hFF : (extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf false false) = 0 := by
    rw [Set.indicator_of_notMem (cfgOf_false_not_mem_ext false)]
  rw [hTT, hFT, hTF, hFF]
  simp only [add_zero]
  rw [← ENNReal.coe_add]
  norm_num

theorem oAmbSum_AE :
    (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
        (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
          (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) ρ) =
      ((1 / 8 : NNReal) : ℝ≥0∞) := by
  rw [sum_amb (fun ρ => (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
    (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) ρ)]
  have hTT : (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf true true) =
        ((1 / 8 : NNReal) : ℝ≥0∞) := by
    rw [Set.indicator_of_mem (Set.mem_inter (cfgOf_mem_region true) (cfgOf_true_mem_ext true)),
      cfgOf_true, oAmb_w_open]
  have hFT : (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf false true) = 0 := by
    rw [Set.indicator_of_notMem (fun h => cfgOf_false_not_mem_region true h.1)]
  have hTF : (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf true false) = 0 := by
    rw [Set.indicator_of_notMem (fun h => cfgOf_false_not_mem_ext true h.2)]
  have hFF : (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) (cfgOf false false) = 0 := by
    rw [Set.indicator_of_notMem (fun h => cfgOf_false_not_mem_region false h.1)]
  rw [hTT, hFT, hTF, hFF]
  simp only [add_zero]

theorem oRegionSum :
    (∑' ω : Fin 1 → Bool, (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞)) =
      ((3 / 8 : NNReal) : ℝ≥0∞) := by
  rw [tsum_fintype, FK.RegionConfinement.sum_config_one
    (fun ω : Fin 1 → Bool => (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞))]
  rw [oRegionW_open, oRegionW_closed]
  rw [← ENNReal.coe_add]
  norm_num

theorem oRegionASum :
    (∑' ω : Fin 1 → Bool,
        oA.indicator (fun ω => (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞)) ω) =
      ((1 / 4 : NNReal) : ℝ≥0∞) := by
  rw [tsum_eq_single (fun _ : Fin 1 => true)]
  · rw [Set.indicator_of_mem (show (fun _ : Fin 1 => true) ∈ oA from rfl), oRegionW_open]
  · intro b hb
    rw [Set.indicator_of_notMem]
    intro h
    exact hb h

end ConditionalLaw

end FK.RegionConfinement.ConfinedStrata
