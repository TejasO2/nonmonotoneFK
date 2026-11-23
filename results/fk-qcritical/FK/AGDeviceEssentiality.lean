import FK.AGBoundedRangeImplant
import FK.FKQuasiTransitiveDevices

/-!
# Essential shared-activation devices on double rays

The one-edge OR gadget in `FK.AGEdgeGadget` constructs an activation which is
pivotal for the existence of an open double ray.  This file proves the same
infinite-event essentiality statement for the bounded-range, shared-activation
model of `FK.AGBoundedRangeImplant`.  The support of the selected device may be
any set containing an edge of the double ray; finiteness is not needed for the
geometric construction.

The witness is explicit.  Its ordinary bonds are the edges of the ray except
for the distinguished closed edge, and all activations are initially off.
Turning the selected activation off leaves the one-gap ray configuration, which
contains no double ray.  Turning it on opens the missing edge and hence the
whole original ray.  Other device supports are arbitrary and play no role.

We then combine this local geometric theorem with the existing separated
packing on a quasi-transitive graph.  Every selected finite template support is
therefore genuinely essential for the infinite double-ray event.  This is not
an assertion of the missing annular rerouting theorem or of a strict critical-
point shift.
-/

open Set
open scoped Sym2

namespace FK.AGImplant

open FK.EssentialEnhancement FK.AGPeeling
open CurvatureVariance.Infra.Percolation

universe u v

/-- The joint state whose bonds are a double ray with one edge closed and whose
activations are all closed. -/
noncomputable def rayDeviceJoint {V : Type u} {G : SimpleGraph V} {F : Type v}
    (r : DoubleRay G) (e : G.edgeSet) : JointConfig G.edgeSet F :=
  Sum.elim (forceEdge r.configuration e false) (fun _ => false)

@[simp] lemma rayDeviceJoint_inl {V : Type u} {G : SimpleGraph V} {F : Type v}
    (r : DoubleRay G) (e f : G.edgeSet) :
    rayDeviceJoint (F := F) r e (Sum.inl f) = forceEdge r.configuration e false f :=
  rfl

@[simp] lemma rayDeviceJoint_inr {V : Type u} {G : SimpleGraph V} {F : Type v}
    (r : DoubleRay G) (e : G.edgeSet) (z : F) :
    rayDeviceJoint r e (Sum.inr z) = false := rfl

/-- With all activations initially closed, forcing one of them closed again
leaves the joint state unchanged. -/
lemma rayDeviceJoint_force_inr_false {V : Type u} {G : SimpleGraph V} {F : Type v}
    (r : DoubleRay G) (e : G.edgeSet) (z : F) :
    forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) false =
      rayDeviceJoint r e := by
  classical
  funext x
  cases x with
  | inl f =>
      rw [forceEdge_of_ne _ (by simp : (Sum.inl f : G.edgeSet ⊕ F) ≠ Sum.inr z)]
  | inr y =>
      by_cases h : y = z
      · subst y
        simp [rayDeviceJoint]
      · rw [forceEdge_of_ne _ (by simp [h] : (Sum.inr y : G.edgeSet ⊕ F) ≠ Sum.inr z)]

/-- In the activation-on ray state, exactly the edges in the selected support
are added by devices. -/
lemma addsEdge_rayDeviceJoint_on_iff {V : Type u} {G : SimpleGraph V} {F : Type v}
    (support : F → Set G.edgeSet) (r : DoubleRay G) (e : G.edgeSet) (z : F)
    (f : G.edgeSet) :
    AddsEdge support (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) true) f ↔
      f ∈ support z := by
  classical
  constructor
  · rintro ⟨y, hy, hfy⟩
    by_cases hyz : y = z
    · simpa [hyz] using hfy
    · have hne : (Sum.inr y : G.edgeSet ⊕ F) ≠ Sum.inr z := by simp [hyz]
      rw [forceEdge_of_ne _ hne, rayDeviceJoint_inr] at hy
      simp at hy
  · intro hf
    exact ⟨z, forceEdge_same _ _ _, hf⟩

/-- Activation-off recovers exactly the original one-gap ray configuration. -/
lemma deviceConfig_rayDeviceJoint_off {V : Type u} {G : SimpleGraph V} {F : Type v}
    (support : F → Set G.edgeSet) (r : DoubleRay G) (e : G.edgeSet) (z : F) :
    deviceConfig support
        (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) false) =
      forceEdge r.configuration e false := by
  classical
  rw [rayDeviceJoint_force_inr_false]
  funext f
  have hnone : ¬ AddsEdge support (rayDeviceJoint (F := F) r e) f := by
    rintro ⟨y, hy, -⟩
    simp [rayDeviceJoint] at hy
  simp only [deviceConfig, hnone, ↓reduceIte, rayDeviceJoint_inl]

/-- An edge in the selected support is open after switching on its device. -/
lemma deviceConfig_rayDeviceJoint_on_of_mem {V : Type u} {G : SimpleGraph V}
    {F : Type v} (support : F → Set G.edgeSet) (r : DoubleRay G)
    (e : G.edgeSet) (z : F) {f : G.edgeSet} (hf : f ∈ support z) :
    deviceConfig support
        (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) true) f = true :=
  deviceConfig_eq_true_of_mem support _ z f (forceEdge_same _ _ _) hf

/-- Outside the selected support, activation-on leaves the one-gap ray bonds
unchanged. -/
lemma deviceConfig_rayDeviceJoint_on_of_not_mem {V : Type u} {G : SimpleGraph V}
    {F : Type v} (support : F → Set G.edgeSet) (r : DoubleRay G)
    (e : G.edgeSet) (z : F) {f : G.edgeSet} (hf : f ∉ support z) :
    deviceConfig support
        (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) true) f =
      forceEdge r.configuration e false f := by
  classical
  have hadds : ¬ AddsEdge support
      (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) true) f := by
    rw [addsEdge_rayDeviceJoint_on_iff]
    exact hf
  simp only [deviceConfig, hadds, ↓reduceIte]
  exact forceEdge_of_ne _ (by simp : (Sum.inl f : G.edgeSet ⊕ F) ≠ Sum.inr z) true

/-- If the selected support contains the closed edge, activation-on restores
the entire original double ray. -/
lemma hasOpenDoubleRay_rayDeviceJoint_on {V : Type u} {G : SimpleGraph V}
    {F : Type v} (support : F → Set G.edgeSet) (r : DoubleRay G)
    {e : G.edgeSet} (z : F) (he : e ∈ support z) :
    HasOpenDoubleRay (deviceConfig support
      (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) true)) := by
  classical
  refine ⟨r, fun n => ?_⟩
  by_cases hn : r.edge n ∈ support z
  · exact deviceConfig_rayDeviceJoint_on_of_mem support r e z hn
  · rw [deviceConfig_rayDeviceJoint_on_of_not_mem support r e z hn]
    have hne : r.edge n ≠ e := by
      intro hne
      apply hn
      rw [hne]
      exact he
    rw [forceEdge_of_ne _ hne]
    exact configuration_edge r n

/-- Genuine infinite-event essentiality of one activation in the shared-
activation device model. -/
def DeviceEssential {V : Type u} {F : Type v} (G : SimpleGraph V)
    (support : F → Set G.edgeSet) (z : F) : Prop :=
  ∃ χ, ActivationPivotal
    (deviceEvent support {ω | HasOpenDoubleRay (G := G) ω}) z χ

/-- **Finite-support shared devices are essential.**  No finiteness assumption
is needed for the geometric statement: any selected support containing an edge
of a double ray gives an activation pivotal for the actual open-double-ray
event. -/
theorem deviceEssential_of_onDoubleRay {V : Type u} {G : SimpleGraph V}
    {F : Type v} (support : F → Set G.edgeSet) (z : F)
    {e : G.edgeSet} (he : e ∈ support z) (hr : OnDoubleRay e) :
    DeviceEssential G support z := by
  obtain ⟨r, k, hk⟩ := hr
  refine ⟨rayDeviceJoint (F := F) r e, ?_, ?_⟩
  · change HasOpenDoubleRay (deviceConfig support
      (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) true))
    exact hasOpenDoubleRay_rayDeviceJoint_on support r z he
  · change ¬ HasOpenDoubleRay (deviceConfig support
      (forceEdge (rayDeviceJoint (F := F) r e) (Sum.inr z) false))
    rw [deviceConfig_rayDeviceJoint_off]
    exact not_hasOpenDoubleRay_update_configuration_false r hk

/-- Every selected device of a separated family whose pivots lie on double
rays is essential in the shared-activation sense. -/
theorem allEssential_deviceEssential_of_separated {V : Type u} {G : SimpleGraph V}
    {S : Set G.edgeSet} {D : G.edgeSet → Finset G.edgeSet}
    (hsep : FKLimit.IsSeparatedDeviceFamily S D)
    (hray : ∀ e ∈ S, OnDoubleRay e) :
    FK.Theorem14.AllEssential
      (fun e => DeviceEssential G (fun f => (↑(D f) : Set G.edgeSet)) e) S := by
  intro e he
  apply deviceEssential_of_onDoubleRay (fun f => (↑(D f) : Set G.edgeSet)) e
  · exact_mod_cast (hsep e he).1
  · exact hray e he

/-- **Separated essential templates on a quasi-transitive graph.**  This keeps
all geometric bounds and translate witnesses of the existing template packing,
and adds genuine infinite-event essentiality for every selected shared
activation. -/
theorem exists_separated_essential_template_devices {V : Type u} (G : SimpleGraph V)
    (hconn : G.Connected) (hqt : FK.QuasiTransitive.IsQuasiTransitive G)
    (T : Finset G.edgeSet) {e₀ : G.edgeSet}
    (he₀ : e₀ ∈ T) (hr₀ : OnDoubleRay e₀) :
    ∃ (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, OnDoubleRay e) ∧
      (∀ e ∈ S, (D e).card ≤ T.card) ∧
      (∀ e ∈ S, ∃ φ : G ≃g G,
        D e = FK.QuasiTransitive.translateSupport φ T ∧ e = φ.mapEdgeSet e₀) ∧
      FK.Theorem14.AllEssential
        (fun e => DeviceEssential G (fun f => (↑(D f) : Set G.edgeSet)) e) S := by
  obtain ⟨S, D, hsep, hbounded, hray, hcard, hwitness⟩ :=
    FK.QuasiTransitive.exists_separated_template_devices G hconn hqt T he₀ hr₀
  exact ⟨S, D, hsep, hbounded, hray, hcard, hwitness,
    allEssential_deviceEssential_of_separated hsep hray⟩

/-- The template theorem specialized to the actual incidence-star devices.
Every selected star activation is essential for the infinite double-ray event. -/
theorem exists_separated_essential_star_devices {V : Type u} (G : SimpleGraph V)
    (hconn : G.Connected) (hqt : FK.QuasiTransitive.IsQuasiTransitive G)
    [G.LocallyFinite] (u₀ : V) {e₀ : G.edgeSet}
    (hu₀ : u₀ ∈ (e₀ : Sym2 V)) (hr₀ : OnDoubleRay e₀) :
    ∃ (Delta : ℕ) (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      (∀ v, G.degree v ≤ Delta) ∧
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, OnDoubleRay e) ∧
      (∀ e ∈ S, (D e).card ≤ Delta) ∧
      (∀ e ∈ S, ∃ v : V,
        D e = FK.QuasiTransitive.starDevice G v ∧ v ∈ (e : Sym2 V)) ∧
      FK.Theorem14.AllEssential
        (fun e => DeviceEssential G (fun f => (↑(D f) : Set G.edgeSet)) e) S := by
  obtain ⟨Delta, S, D, hDelta, hsep, hbounded, hray, hcard, hwitness⟩ :=
    FK.QuasiTransitive.exists_separated_star_devices G hconn hqt u₀ hu₀ hr₀
  exact ⟨Delta, S, D, hDelta, hsep, hbounded, hray, hcard, hwitness,
    allEssential_deviceEssential_of_separated hsep hray⟩

/-- The template theorem specialized to genuine simple-cycle supports.  Every
selected shared cycle activation is essential for the infinite double-ray
event, while the supplied cycle length and geometric witnesses are retained. -/
theorem exists_separated_essential_cycle_devices {V : Type u} (G : SimpleGraph V)
    (hconn : G.Connected) (hqt : FK.QuasiTransitive.IsQuasiTransitive G)
    {u₀ : V} (c₀ : G.Walk u₀ u₀) (hc₀ : c₀.IsCycle) {e₀ : G.edgeSet}
    (he₀ : (e₀ : Sym2 V) ∈ c₀.edges) (hr₀ : OnDoubleRay e₀) :
    ∃ (L : ℕ) (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      L = c₀.length ∧
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, OnDoubleRay e) ∧
      (∀ e ∈ S, (D e).card ≤ L) ∧
      (∀ e ∈ S, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
        D e = FK.QuasiTransitive.walkDevice c ∧ (e : Sym2 V) ∈ c.edges) ∧
      FK.Theorem14.AllEssential
        (fun e => DeviceEssential G (fun f => (↑(D f) : Set G.edgeSet)) e) S := by
  obtain ⟨L, S, D, hL, hsep, hbounded, hray, hcard, hwitness⟩ :=
    FK.QuasiTransitive.exists_separated_cycle_devices G hconn hqt c₀ hc₀ he₀ hr₀
  exact ⟨L, S, D, hL, hsep, hbounded, hray, hcard, hwitness,
    allEssential_deviceEssential_of_separated hsep hray⟩

/-- A support-contained annulus needs no auxiliary rerouting hypothesis: the
activated device opens every edge whose two endpoints must be reconnected.
The exact finite transport constants and actual open-connection event are
unchanged. -/
theorem openConnected_annular_edgePivotal_event_mul_le_of_support_subset
    {V : Type u} {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    {F : Type v} [Fintype F] [DecidableEq F]
    (bond : G.edgeSet → OpenPath.FinProb Bool) (activation : F → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    {u v a b : V} (huv : G.Adj u v)
    (R : Finset G.edgeSet)
    (he : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ R)
    (support : F → Set G.edgeSet) (z : F)
    (hR : ∀ f ∈ R, f ∈ support z) :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ R.card * μ.event {χ | EdgePivotal
        (deviceEvent support {ω | OpenConnected G ω Set.univ a b})
        (⟨s(u, v), huv⟩ : G.edgeSet) χ} ≤
      ((2 ^ R.card : ℕ) : ℝ) * μ.event {χ | ActivationPivotal
        (deviceEvent support {ω | OpenConnected G ω Set.univ a b}) z χ} := by
  classical
  dsimp only
  apply openConnected_annular_edgePivotal_event_mul_le bond activation δ hδ
    hbond hactivation huv R he support z
  intro χ x y hxy _hopen hfR
  apply OpenConnected.of_adj hxy (Set.mem_univ _)
  exact deviceConfig_eq_true_of_mem support _ z _ (forceEdge_same _ _ _) (hR _ hfR)

/-- The support-contained annular criterion for the actual finite-volume
one-arm event, with the same independent joint bond/activation law. -/
theorem deviceArmEvent_annular_edgePivotal_event_mul_le_of_support_subset
    {V : Type u} {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    {F : Type v} [Fintype F] [DecidableEq F]
    (bond : G.edgeSet → OpenPath.FinProb Bool) (activation : F → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    {u v o : V} (huv : G.Adj u v)
    (R : Finset G.edgeSet)
    (he : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ R)
    (support : F → Set G.edgeSet) (z : F) (n : ℕ)
    (hR : ∀ f ∈ R, f ∈ support z) :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ R.card * μ.event {χ | EdgePivotal (deviceArmEvent G support o n)
        (⟨s(u, v), huv⟩ : G.edgeSet) χ} ≤
      ((2 ^ R.card : ℕ) : ℝ) * μ.event {χ |
        ActivationPivotal (deviceArmEvent G support o n) z χ} := by
  classical
  dsimp only
  apply deviceArmEvent_annular_edgePivotal_event_mul_le bond activation δ hδ
    hbond hactivation huv R he support z n
  intro χ x y hxy _hopen hfR
  apply OpenConnected.of_adj hxy (Set.mem_univ _)
  exact deviceConfig_eq_true_of_mem support _ z _ (forceEdge_same _ _ _) (hR _ hfR)

end FK.AGImplant
