import FK.AGEdgeGadget
import FK.CycleEnhancement

/-!
# Bounded-range route implants for activation pivots

The one-edge OR gadget in `FK.AGEdgeGadget` has an independent activation for
each edge. This file treats a different bounded-range device: one activation
opens every edge in its support, and the same activation is shared by all
those edges. A finite walk contained in that support is an explicit route
implant.

The main deterministic theorem converts a bond pivot for an actual open
connection event into an activation pivot after closing only the original
bond. For activation-off, monotonicity suffices: no auxiliary edge is opened.
For activation-on, an explicit walk-replacement lemma substitutes the
implanted route for every traversal of the original bond, in either direction.

The probability theorem applies the existing normalized finite product
transport with its exact `δ` likelihood ratio and fibre bound `2`. There is no
assertion about arbitrary essential enhancements, a global expected-pivot
comparison, differential integration, or a strict critical-point shift.
-/

open Set
open scoped BigOperators Sym2

namespace FK.AGImplant

open FK.EssentialEnhancement FK.AGPeeling
open CurvatureVariance.Infra.Percolation

universe u v w

/-- Activation of at least one device whose support contains `e` adds `e`. -/
def AddsEdge {E : Type u} {F : Type v} (support : F → Set E)
    (χ : JointConfig E F) (e : E) : Prop :=
  ∃ z, χ (Sum.inr z) = true ∧ e ∈ support z

/-- A bounded-range device model with shared activations. An ordinary bond at
`e` is retained, and every active device whose support contains `e` opens it. -/
noncomputable def deviceConfig {E : Type u} {F : Type v} (support : F → Set E)
    (χ : JointConfig E F) : E → Bool := fun e => by
  classical
  exact if AddsEdge support χ e then true else χ (Sum.inl e)

lemma deviceConfig_eq_true_of_mem {E : Type u} {F : Type v}
    (support : F → Set E) (χ : JointConfig E F) (z : F) (e : E)
    (hz : χ (Sum.inr z) = true) (he : e ∈ support z) :
    deviceConfig support χ e = true := by
  classical
  unfold deviceConfig
  split_ifs with h
  · rfl
  · exact (h ⟨z, hz, he⟩).elim

/-- Coordinatewise monotonicity, exposing the bond and activation inputs. -/
lemma deviceConfig_mono_at {E : Type u} {F : Type v} (support : F → Set E)
    {χ ξ : JointConfig E F} (e : E)
    (hbond : χ (Sum.inl e) ≤ ξ (Sum.inl e))
    (hactivation : ∀ z, χ (Sum.inr z) ≤ ξ (Sum.inr z)) :
    deviceConfig support χ e ≤ deviceConfig support ξ e := by
  classical
  by_cases hξ : AddsEdge support ξ e
  · simp [deviceConfig, hξ]
  · have hχ : ¬ AddsEdge support χ e := by
      rintro ⟨z, hz, he⟩
      apply hξ
      refine ⟨z, ?_, he⟩
      have hle := hactivation z
      rw [hz] at hle
      exact top_unique hle
    simpa [deviceConfig, hχ, hξ] using hbond

lemma deviceConfig_mono {E : Type u} {F : Type v} (support : F → Set E)
    {χ ξ : JointConfig E F} (hχξ : χ ≤ ξ) :
    deviceConfig support χ ≤ deviceConfig support ξ := by
  intro e
  exact deviceConfig_mono_at support e (hχξ (Sum.inl e)) (fun z => hχξ (Sum.inr z))

/-- Pull back an event on enhanced bonds to the joint bond/device state. -/
def deviceEvent {E : Type u} {F : Type v} (support : F → Set E)
    (B : Set (E → Bool)) : Set (JointConfig E F) :=
  deviceConfig support ⁻¹' B

lemma isUpperSet_deviceEvent {E : Type u} {F : Type v} (support : F → Set E)
    {B : Set (E → Bool)} (hB : IsUpperSet B) :
    IsUpperSet (deviceEvent support B) := by
  intro χ ξ hχξ hχ
  exact hB (deviceConfig_mono support hχξ) hχ

/-- Toggling one device has no effect outside its support. -/
lemma addsEdge_force_activation_iff_of_notMem {E : Type u} {F : Type v}
    (support : F → Set E) (χ : JointConfig E F) (z : F) (b : Bool) {e : E}
    (he : e ∉ support z) :
    AddsEdge support (forceEdge χ (Sum.inr z) b) e ↔ AddsEdge support χ e := by
  classical
  constructor
  · rintro ⟨y, hy, hey⟩
    have hyz : y ≠ z := by
      rintro rfl
      exact he hey
    have hne : (Sum.inr y : E ⊕ F) ≠ Sum.inr z := by simp [hyz]
    exact ⟨y, (forceEdge_of_ne χ hne b).symm.trans hy, hey⟩
  · rintro ⟨y, hy, hey⟩
    have hyz : y ≠ z := by
      rintro rfl
      exact he hey
    have hne : (Sum.inr y : E ⊕ F) ≠ Sum.inr z := by simp [hyz]
    exact ⟨y, (forceEdge_of_ne χ hne b).trans hy, hey⟩

lemma deviceConfig_force_activation_outside {E : Type u} {F : Type v}
    (support : F → Set E) (χ : JointConfig E F) (z : F) (b : Bool) {e : E}
    (he : e ∉ support z) :
    deviceConfig support (forceEdge χ (Sum.inr z) b) e = deviceConfig support χ e := by
  classical
  simp only [deviceConfig, addsEdge_force_activation_iff_of_notMem support χ z b he]
  rw [forceEdge_of_ne χ (by simp : (Sum.inl e : E ⊕ F) ≠ Sum.inr z) b]

/-- The local modification: close the pivotal bond and leave every activation
and every other bond untouched. -/
noncomputable def implantClose {E : Type u} {F : Type v} (e : E) :
    JointConfig E F → JointConfig E F := fun χ =>
  forceEdge χ (Sum.inl e) false

lemma implantClose_isLocalModification {E : Type u} {F : Type v}
    [DecidableEq E] (e : E) :
    IsLocalModification {Sum.inl e} (implantClose (F := F) e) := by
  classical
  intro χ x hx
  have hxe : x ≠ (Sum.inl e : E ⊕ F) := by simpa using hx
  exact forceEdge_of_ne χ hxe false

/-- Open connections are symmetric, including in a restricted edge set. -/
lemma openConnected_reverse {V : Type w} {G : SimpleGraph V}
    {ω : G.edgeSet → Bool} {A : Set (Sym2 V)} {u v : V}
    (h : OpenConnected G ω A u v) : OpenConnected G ω A v u := by
  obtain ⟨p, hp⟩ := h
  induction p with
  | nil => exact OpenConnected.refl _ _ _
  | @cons u v w huv p ih =>
      rw [isOpenIn_cons] at hp
      have htail : OpenConnected G ω A w v := ih hp.2
      have hhead : OpenConnected G ω A v u := by
        apply OpenConnected.of_adj huv.symm
        · simpa only [Sym2.eq_swap] using hp.1.1
        · simpa only [Sym2.eq_swap] using hp.1.2
      exact htail.trans hhead

/-- Replace an edge by an actual open walk joining its endpoints. Other open
edges are preserved, with either orientation and repeated traversals allowed. -/
lemma openConnected_replaceEdge {V : Type w} {G : SimpleGraph V}
    {u v a b : V} (huv : G.Adj u v) {ω ξ : G.edgeSet → Bool}
    (hother : ∀ f, f ≠ (⟨s(u, v), huv⟩ : G.edgeSet) →
      ω f = true → ξ f = true)
    (himplant : OpenConnected G ξ Set.univ u v)
    (hconn : OpenConnected G ω Set.univ a b) :
    OpenConnected G ξ Set.univ a b := by
  obtain ⟨p, hp⟩ := hconn
  induction p with
  | nil => exact OpenConnected.refl _ _ _
  | @cons x y z hxy q ih =>
      rw [isOpenIn_cons] at hp
      by_cases he : (⟨s(x, y), hxy⟩ : G.edgeSet) = ⟨s(u, v), huv⟩
      · have hval : s(x, y) = s(u, v) := congrArg Subtype.val he
        rcases Sym2.eq_iff.mp hval with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
        · subst x
          subst y
          exact himplant.trans (ih hp.2)
        · subst x
          subst y
          exact (openConnected_reverse himplant).trans (ih hp.2)
      · exact (OpenConnected.of_adj hxy (Set.mem_univ _)
          (hother _ he hp.1.2)).trans (ih hp.2)

/-- Activation-on after the local modification retains an open connection. -/
lemma openConnected_implantClose_on {V : Type w} {G : SimpleGraph V}
    {u v a b : V} (huv : G.Adj u v) {F : Type v}
    (support : F → Set G.edgeSet) (z : F) (route : G.Walk u v)
    (hroute : ∀ f : G.edgeSet, (f : Sym2 V) ∈ route.edges → f ∈ support z)
    (χ : JointConfig G.edgeSet F)
    (hconn : OpenConnected G
      (deviceConfig support (forceEdge χ
        (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) true)) Set.univ a b) :
    OpenConnected G
      (deviceConfig support (forceEdge (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ)
        (Sum.inr z) true)) Set.univ a b := by
  classical
  apply openConnected_replaceEdge huv (ω := deviceConfig support
    (forceEdge χ (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) true))
  · intro f hf hopen
    have hle := deviceConfig_mono_at support f (χ := forceEdge χ
      (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) true)
      (ξ := forceEdge (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ)
        (Sum.inr z) true) ?_ ?_
    · rw [hopen] at hle
      exact top_unique hle
    · have hne : (Sum.inl f : G.edgeSet ⊕ F) ≠
          Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet) := by simpa using hf
      simp [implantClose, forceEdge, hne]
    · intro y
      have hle := le_forceEdge_true
        (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ) (Sum.inr z)
      have hy := hle (Sum.inr y)
      simpa only [implantClose, forceEdge_of_ne _ (by simp :
        (Sum.inr y : G.edgeSet ⊕ F) ≠ Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet))] using hy
  · refine ⟨route, ?_⟩
    intro d hd
    refine ⟨Set.mem_univ _, ?_⟩
    apply deviceConfig_eq_true_of_mem support _ z
    · exact forceEdge_same _ _ _
    · apply hroute
      exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · exact hconn

/-- Activation-off after the local modification is below the original
enhanced configuration with the bond forced closed. -/
lemma deviceConfig_implantClose_off_le {V : Type w} {G : SimpleGraph V}
    {u v : V} (huv : G.Adj u v) {F : Type v}
    (support : F → Set G.edgeSet) (z : F) (χ : JointConfig G.edgeSet F) :
    deviceConfig support
        (forceEdge (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ) (Sum.inr z) false) ≤
      deviceConfig support (forceEdge χ
        (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) false) := by
  have hle := forceEdge_false_le
    (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ) (Sum.inr z)
  exact deviceConfig_mono support hle

/-- **Cycle/route implant.** If the support of `z` contains an actual walk
joining the endpoints of a bond, then a bond pivot for an open-connection
event becomes an activation pivot after closing only that bond. -/
theorem activationPivotal_openConnected_implantClose {V : Type w}
    {G : SimpleGraph V} {u v a b : V} (huv : G.Adj u v) {F : Type v}
    (support : F → Set G.edgeSet) (z : F) (route : G.Walk u v)
    (hroute : ∀ f : G.edgeSet, (f : Sym2 V) ∈ route.edges → f ∈ support z)
    {χ : JointConfig G.edgeSet F}
    (hpiv : EdgePivotal
      (deviceEvent support {ω | OpenConnected G ω Set.univ a b})
      (⟨s(u, v), huv⟩ : G.edgeSet) χ) :
    ActivationPivotal
      (deviceEvent support {ω | OpenConnected G ω Set.univ a b}) z
      (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ) := by
  constructor
  · exact openConnected_implantClose_on huv support z route hroute χ hpiv.1
  · intro hmem
    apply hpiv.2
    exact OpenConnected.mono_config hmem
      (deviceConfig_implantClose_off_le huv support z χ)

/-- The same route implant for an existential open-connection event. -/
theorem activationPivotal_exists_openConnected_implantClose {V : Type w}
    {G : SimpleGraph V} {u v o : V} (huv : G.Adj u v) {F : Type v}
    (W : Set V) (support : F → Set G.edgeSet) (z : F) (route : G.Walk u v)
    (hroute : ∀ f : G.edgeSet, (f : Sym2 V) ∈ route.edges → f ∈ support z)
    {χ : JointConfig G.edgeSet F}
    (hpiv : EdgePivotal
      (deviceEvent support {ω | ∃ w ∈ W, OpenConnected G ω Set.univ o w})
      (⟨s(u, v), huv⟩ : G.edgeSet) χ) :
    ActivationPivotal
      (deviceEvent support {ω | ∃ w ∈ W, OpenConnected G ω Set.univ o w}) z
      (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ) := by
  constructor
  · obtain ⟨w, hw, hconn⟩ := hpiv.1
    exact ⟨w, hw, openConnected_implantClose_on huv support z route hroute χ hconn⟩
  · intro hmem
    apply hpiv.2
    exact (isUpperSet_exists_openConnected (G := G) Set.univ o W)
      (deviceConfig_implantClose_off_le huv support z χ) hmem

/-- The actual finite-volume one-arm event under shared-activation devices. -/
def deviceArmEvent {V : Type w} (G : SimpleGraph V) {F : Type v}
    (support : F → Set G.edgeSet) (o : V) (n : ℕ) :
    Set (JointConfig G.edgeSet F) :=
  deviceEvent support (armEvent G o n)

lemma isUpperSet_deviceArmEvent {V : Type w} (G : SimpleGraph V) {F : Type v}
    (support : F → Set G.edgeSet) (o : V) (n : ℕ) :
    IsUpperSet (deviceArmEvent G support o n) :=
  isUpperSet_deviceEvent support (isUpperSet_armEvent o n)

/-- Route implantation for the repository's actual `armEvent`. -/
theorem activationPivotal_deviceArmEvent_implantClose {V : Type w}
    {G : SimpleGraph V} {u v o : V} (huv : G.Adj u v) {F : Type v}
    (support : F → Set G.edgeSet) (z : F) (route : G.Walk u v)
    (hroute : ∀ f : G.edgeSet, (f : Sym2 V) ∈ route.edges → f ∈ support z)
    (n : ℕ) {χ : JointConfig G.edgeSet F}
    (hpiv : EdgePivotal (deviceArmEvent G support o n)
      (⟨s(u, v), huv⟩ : G.edgeSet) χ) :
    ActivationPivotal (deviceArmEvent G support o n) z
      (implantClose (⟨s(u, v), huv⟩ : G.edgeSet) χ) := by
  constructor
  · obtain ⟨w, hw, hconn⟩ := hpiv.1
    exact ⟨w, hw, openConnected_implantClose_on huv support z route hroute χ hconn⟩
  · intro hmem
    apply hpiv.2
    exact (isUpperSet_armEvent o n)
      (deviceConfig_implantClose_off_le huv support z χ) hmem

/-- Specialization to the actual edge finset of an auxiliary walk. -/
theorem activationPivotal_walkDevice_openConnected {V : Type w}
    {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq V]
    {u v a b : V} (huv : G.Adj u v) {F : Type v} (z : F)
    (route : G.Walk v u) {χ : JointConfig G.edgeSet F}
    (hpiv : EdgePivotal
      (deviceEvent (fun _ : F =>
        (↑(OpenPath.walkEdgeFinset route) : Set G.edgeSet))
        {ω | OpenConnected G ω Set.univ a b}) (OpenPath.cycleHeadEdge huv) χ) :
    ActivationPivotal
      (deviceEvent (fun _ : F =>
        (↑(OpenPath.walkEdgeFinset route) : Set G.edgeSet))
        {ω | OpenConnected G ω Set.univ a b}) z
      (implantClose (OpenPath.cycleHeadEdge huv) χ) := by
  apply activationPivotal_openConnected_implantClose huv _ z route.reverse _ hpiv
  intro f hf
  have hf' : (f : Sym2 V) ∈ route.edges := by
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hf
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf'⟩

open OpenPath

/-- **Normalized finite-product comparison for a route implant.** The
one-coordinate modification yields likelihood ratio `δ` and fibre bound `2`. -/
theorem openConnected_edgePivotal_event_mul_le {V : Type w}
    {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    {F : Type v} [Fintype F] [DecidableEq F]
    (bond : G.edgeSet → FinProb Bool) (activation : F → FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    {u v a b : V} (huv : G.Adj u v)
    (support : F → Set G.edgeSet) (z : F) (route : G.Walk u v)
    (hroute : ∀ f : G.edgeSet, (f : Sym2 V) ∈ route.edges → f ∈ support z) :
    let μ := FinProb.pi (Sum.elim bond activation)
    δ * μ.event {χ | EdgePivotal
        (deviceEvent support {ω | OpenConnected G ω Set.univ a b})
        (⟨s(u, v), huv⟩ : G.edgeSet) χ} ≤
      2 * μ.event {χ | ActivationPivotal
        (deviceEvent support {ω | OpenConnected G ω Set.univ a b}) z χ} := by
  classical
  dsimp only
  have h := local_joint_edgePivotal_event_mul_le bond activation
    {Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)} δ hδ hbond hactivation
    (implantClose (⟨s(u, v), huv⟩ : G.edgeSet))
    (implantClose_isLocalModification (⟨s(u, v), huv⟩ : G.edgeSet))
    (deviceEvent support {ω | OpenConnected G ω Set.univ a b})
    (⟨s(u, v), huv⟩ : G.edgeSet) [z]
    (fun χ hpiv => ⟨z, by simp,
      activationPivotal_openConnected_implantClose huv support z route hroute hpiv⟩)
  simpa using h

/-- The normalized finite-product comparison specialized to the actual
finite-volume `armEvent`. -/
theorem deviceArmEvent_edgePivotal_event_mul_le {V : Type w}
    {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    {F : Type v} [Fintype F] [DecidableEq F]
    (bond : G.edgeSet → FinProb Bool) (activation : F → FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    {u v o : V} (huv : G.Adj u v)
    (support : F → Set G.edgeSet) (z : F) (route : G.Walk u v)
    (hroute : ∀ f : G.edgeSet, (f : Sym2 V) ∈ route.edges → f ∈ support z)
    (n : ℕ) :
    let μ := FinProb.pi (Sum.elim bond activation)
    δ * μ.event {χ | EdgePivotal (deviceArmEvent G support o n)
        (⟨s(u, v), huv⟩ : G.edgeSet) χ} ≤
      2 * μ.event {χ | ActivationPivotal (deviceArmEvent G support o n) z χ} := by
  classical
  dsimp only
  have h := local_joint_edgePivotal_event_mul_le bond activation
    {Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)} δ hδ hbond hactivation
    (implantClose (⟨s(u, v), huv⟩ : G.edgeSet))
    (implantClose_isLocalModification (⟨s(u, v), huv⟩ : G.edgeSet))
    (deviceArmEvent G support o n) (⟨s(u, v), huv⟩ : G.edgeSet) [z]
    (fun χ hpiv => ⟨z, by simp,
      activationPivotal_deviceArmEvent_implantClose huv support z route hroute n hpiv⟩)
  simpa using h

end FK.AGImplant

namespace FK.AGImplant

open FK.EssentialEnhancement FK.AGPeeling
open CurvatureVariance.Infra.Percolation
open OpenPath

universe u v w

/-- General open-walk surgery. If every source-open edge has its endpoints
connected in the target, then every source open connection persists. The
replacement walks may be arbitrarily large and need not be edge disjoint. -/
lemma openConnected_surgery {V : Type w} {G : SimpleGraph V}
    {ω ξ : G.edgeSet → Bool} {a b : V}
    (hstep : ∀ {x y : V} (hxy : G.Adj x y),
      ω ⟨s(x, y), hxy⟩ = true → OpenConnected G ξ Set.univ x y)
    (hconn : OpenConnected G ω Set.univ a b) :
    OpenConnected G ξ Set.univ a b := by
  obtain ⟨p, hp⟩ := hconn
  induction p with
  | nil => exact OpenConnected.refl _ _ _
  | @cons x y z hxy q ih =>
      rw [isOpenIn_cons] at hp
      exact (hstep hxy hp.1.2).trans (ih hp.2)

/-- Close every bond in a finite annular set and leave all activations fixed. -/
noncomputable def annularClose {E : Type u} {F : Type v} (R : Finset E)
    (χ : JointConfig E F) : JointConfig E F := by
  classical
  exact fun x => match x with
    | Sum.inl e => if e ∈ R then false else χ (Sum.inl e)
    | Sum.inr z => χ (Sum.inr z)

@[simp] lemma annularClose_inr {E : Type u} {F : Type v} (R : Finset E)
    (χ : JointConfig E F) (z : F) :
    annularClose R χ (Sum.inr z) = χ (Sum.inr z) := rfl

lemma annularClose_le {E : Type u} {F : Type v} (R : Finset E)
    (χ : JointConfig E F) : annularClose R χ ≤ χ := by
  classical
  intro x
  cases x with
  | inl e =>
      by_cases he : e ∈ R <;> simp [annularClose, he]
  | inr z => exact le_rfl

lemma annularClose_le_forceEdge_false {E : Type u} {F : Type v}
    (R : Finset E) (e : E) (he : e ∈ R) (χ : JointConfig E F) :
    annularClose R χ ≤ forceEdge χ (Sum.inl e) false := by
  classical
  intro x
  cases x with
  | inl f =>
      by_cases hfe : f = e
      · subst f
        simp [annularClose, he]
      · by_cases hfR : f ∈ R
        · simp [annularClose, hfR]
        · have hne : (Sum.inl f : E ⊕ F) ≠ Sum.inl e := by simpa using hfe
          simp [annularClose, hfR, forceEdge_of_ne _ hne]
  | inr z =>
      rw [annularClose_inr,
        forceEdge_of_ne χ (by simp : (Sum.inr z : E ⊕ F) ≠ Sum.inl e) false]

/-- The bond coordinates in a finite annulus, as coordinates of the joint
bond/activation space. -/
def bondCoordinates {E : Type u} {F : Type v} (R : Finset E) : Finset (E ⊕ F) :=
  R.map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] lemma card_bondCoordinates {E : Type u} {F : Type v} (R : Finset E) :
    (bondCoordinates (F := F) R).card = R.card := by
  simp [bondCoordinates]

lemma annularClose_isLocalModification {E : Type u} {F : Type v}
    [DecidableEq E] (R : Finset E) :
    IsLocalModification (bondCoordinates (F := F) R) (annularClose R) := by
  classical
  intro χ x hx
  cases x with
  | inl e =>
      simp only [annularClose]
      split_ifs with he
      · exact False.elim (hx (by simp [bondCoordinates, he]))
      · rfl
  | inr z => rfl

/-- Outside the annulus, activation-on retains every source-open enhanced
edge. Bonds are unchanged there and activations can only increase. -/
lemma deviceConfig_annular_on_eq_true_of_notMem {E : Type u} {F : Type v}
    (support : F → Set E) (R : Finset E) (e : E) (he : e ∈ R) (z : F)
    (χ : JointConfig E F) (f : E) (hf : f ∉ R)
    (hopen : deviceConfig support (forceEdge χ (Sum.inl e) true) f = true) :
    deviceConfig support (forceEdge (annularClose R χ) (Sum.inr z) true) f = true := by
  classical
  have hle := deviceConfig_mono_at support f
    (χ := forceEdge χ (Sum.inl e) true)
    (ξ := forceEdge (annularClose R χ) (Sum.inr z) true) ?_ ?_
  · rw [hopen] at hle
    exact top_unique hle
  · have hfe : f ≠ e := by
      rintro rfl
      exact hf he
    simp [annularClose, forceEdge, hf, hfe]
  · intro y
    have hle := le_forceEdge_true (annularClose R χ) (Sum.inr z) (Sum.inr y)
    simpa only [annularClose_inr, forceEdge_of_ne _ (by simp :
      (Sum.inr y : E ⊕ F) ≠ Sum.inl e)] using hle

/-- With the pivotal bond in the annulus, activation-off after annular closure
is below the original enhanced bond-closed configuration. -/
lemma deviceConfig_annularClose_off_le {E : Type u} {F : Type v}
    (support : F → Set E) (R : Finset E) (e : E) (he : e ∈ R)
    (z : F) (χ : JointConfig E F) :
    deviceConfig support (forceEdge (annularClose R χ) (Sum.inr z) false) ≤
      deviceConfig support (forceEdge χ (Sum.inl e) false) := by
  calc
    deviceConfig support (forceEdge (annularClose R χ) (Sum.inr z) false) ≤
        deviceConfig support (annularClose R χ) :=
      deviceConfig_mono support (forceEdge_false_le _ _)
    _ ≤ deviceConfig support (forceEdge χ (Sum.inl e) false) :=
      deviceConfig_mono support (annularClose_le_forceEdge_false R e he χ)

/-- **Finite annular route replacement.** The hypothesis `hreplace` is purely
local: for every source-open enhanced edge whose bond is closed in `R`, it
requires an actual target-open walk between that edge's endpoints. Edges
outside `R` are preserved automatically. -/
theorem activationPivotal_openConnected_annularClose {V : Type w}
    {G : SimpleGraph V} {u v a b : V} (huv : G.Adj u v) {F : Type v}
    (R : Finset G.edgeSet) (he : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ R)
    (support : F → Set G.edgeSet) (z : F) {χ : JointConfig G.edgeSet F}
    (hreplace : ∀ {x y : V} (hxy : G.Adj x y),
      deviceConfig support (forceEdge χ
        (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) true) ⟨s(x, y), hxy⟩ = true →
      (⟨s(x, y), hxy⟩ : G.edgeSet) ∈ R →
      OpenConnected G
        (deviceConfig support (forceEdge (annularClose R χ) (Sum.inr z) true))
        Set.univ x y)
    (hpiv : EdgePivotal
      (deviceEvent support {ω | OpenConnected G ω Set.univ a b})
      (⟨s(u, v), huv⟩ : G.edgeSet) χ) :
    ActivationPivotal
      (deviceEvent support {ω | OpenConnected G ω Set.univ a b}) z
      (annularClose R χ) := by
  constructor
  · apply openConnected_surgery (ξ := deviceConfig support
      (forceEdge (annularClose R χ) (Sum.inr z) true)) ?_ hpiv.1
    intro x y hxy hopen
    by_cases hfR : (⟨s(x, y), hxy⟩ : G.edgeSet) ∈ R
    · exact hreplace hxy hopen hfR
    · exact OpenConnected.of_adj hxy (Set.mem_univ _)
        (deviceConfig_annular_on_eq_true_of_notMem support R _ he z χ _ hfR hopen)
  · intro hmem
    apply hpiv.2
    exact OpenConnected.mono_config hmem
      (deviceConfig_annularClose_off_le support R _ he z χ)

/-- The finite annular construction for the actual `armEvent`. -/
theorem activationPivotal_deviceArmEvent_annularClose {V : Type w}
    {G : SimpleGraph V} {u v o : V} (huv : G.Adj u v) {F : Type v}
    (R : Finset G.edgeSet) (he : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ R)
    (support : F → Set G.edgeSet) (z : F) (n : ℕ)
    {χ : JointConfig G.edgeSet F}
    (hreplace : ∀ {x y : V} (hxy : G.Adj x y),
      deviceConfig support (forceEdge χ
        (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) true) ⟨s(x, y), hxy⟩ = true →
      (⟨s(x, y), hxy⟩ : G.edgeSet) ∈ R →
      OpenConnected G
        (deviceConfig support (forceEdge (annularClose R χ) (Sum.inr z) true))
        Set.univ x y)
    (hpiv : EdgePivotal (deviceArmEvent G support o n)
      (⟨s(u, v), huv⟩ : G.edgeSet) χ) :
    ActivationPivotal (deviceArmEvent G support o n) z (annularClose R χ) := by
  constructor
  · obtain ⟨w, hw, hconn⟩ := hpiv.1
    refine ⟨w, hw, ?_⟩
    apply openConnected_surgery (ξ := deviceConfig support
      (forceEdge (annularClose R χ) (Sum.inr z) true)) ?_ hconn
    intro x y hxy hopen
    by_cases hfR : (⟨s(x, y), hxy⟩ : G.edgeSet) ∈ R
    · exact hreplace hxy hopen hfR
    · exact OpenConnected.of_adj hxy (Set.mem_univ _)
        (deviceConfig_annular_on_eq_true_of_notMem support R _ he z χ _ hfR hopen)
  · intro hmem
    apply hpiv.2
    exact (isUpperSet_armEvent o n)
      (deviceConfig_annularClose_off_le support R _ he z χ) hmem

/-- **Bounded-fibre annular comparison.** The exact likelihood ratio is
`δ ^ R.card` and the source-fibre bound is `2 ^ R.card`, as obtained from the
actual finite independent product law. -/
theorem openConnected_annular_edgePivotal_event_mul_le {V : Type w}
    {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    {F : Type v} [Fintype F] [DecidableEq F]
    (bond : G.edgeSet → FinProb Bool) (activation : F → FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    {u v a b : V} (huv : G.Adj u v)
    (R : Finset G.edgeSet) (he : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ R)
    (support : F → Set G.edgeSet) (z : F)
    (hreplace : ∀ (χ : JointConfig G.edgeSet F) {x y : V} (hxy : G.Adj x y),
      deviceConfig support (forceEdge χ
        (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) true) ⟨s(x, y), hxy⟩ = true →
      (⟨s(x, y), hxy⟩ : G.edgeSet) ∈ R →
      OpenConnected G
        (deviceConfig support (forceEdge (annularClose R χ) (Sum.inr z) true))
        Set.univ x y) :
    let μ := FinProb.pi (Sum.elim bond activation)
    δ ^ R.card * μ.event {χ | EdgePivotal
        (deviceEvent support {ω | OpenConnected G ω Set.univ a b})
        (⟨s(u, v), huv⟩ : G.edgeSet) χ} ≤
      ((2 ^ R.card : ℕ) : ℝ) * μ.event {χ | ActivationPivotal
        (deviceEvent support {ω | OpenConnected G ω Set.univ a b}) z χ} := by
  classical
  dsimp only
  have h := local_joint_edgePivotal_event_mul_le bond activation
    (bondCoordinates (F := F) R) δ hδ hbond hactivation (annularClose R)
    (annularClose_isLocalModification R)
    (deviceEvent support {ω | OpenConnected G ω Set.univ a b})
    (⟨s(u, v), huv⟩ : G.edgeSet) [z]
    (fun χ hpiv => ⟨z, by simp,
      activationPivotal_openConnected_annularClose huv R he support z
        (hreplace χ) hpiv⟩)
  simpa using h

/-- Bounded-fibre annular comparison for the actual `armEvent`. -/
theorem deviceArmEvent_annular_edgePivotal_event_mul_le {V : Type w}
    {G : SimpleGraph V} [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    {F : Type v} [Fintype F] [DecidableEq F]
    (bond : G.edgeSet → FinProb Bool) (activation : F → FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    {u v o : V} (huv : G.Adj u v)
    (R : Finset G.edgeSet) (he : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ R)
    (support : F → Set G.edgeSet) (z : F) (n : ℕ)
    (hreplace : ∀ (χ : JointConfig G.edgeSet F) {x y : V} (hxy : G.Adj x y),
      deviceConfig support (forceEdge χ
        (Sum.inl (⟨s(u, v), huv⟩ : G.edgeSet)) true) ⟨s(x, y), hxy⟩ = true →
      (⟨s(x, y), hxy⟩ : G.edgeSet) ∈ R →
      OpenConnected G
        (deviceConfig support (forceEdge (annularClose R χ) (Sum.inr z) true))
        Set.univ x y) :
    let μ := FinProb.pi (Sum.elim bond activation)
    δ ^ R.card * μ.event {χ | EdgePivotal (deviceArmEvent G support o n)
        (⟨s(u, v), huv⟩ : G.edgeSet) χ} ≤
      ((2 ^ R.card : ℕ) : ℝ) * μ.event {χ |
        ActivationPivotal (deviceArmEvent G support o n) z χ} := by
  classical
  dsimp only
  have h := local_joint_edgePivotal_event_mul_le bond activation
    (bondCoordinates (F := F) R) δ hδ hbond hactivation (annularClose R)
    (annularClose_isLocalModification R) (deviceArmEvent G support o n)
    (⟨s(u, v), huv⟩ : G.edgeSet) [z]
    (fun χ hpiv => ⟨z, by simp,
      activationPivotal_deviceArmEvent_annularClose huv R he support z n
        (hreplace χ) hpiv⟩)
  simpa using h

end FK.AGImplant
