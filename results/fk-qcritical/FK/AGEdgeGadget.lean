import FK.AGPivotTransport
import FK.MargulisRussoFinite
import FK.OrderedFinite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# An explicit edge enhancement gadget for AG pivot transport

This module treats the elementary stochastic edge enhancement which opens an
edge when either its bond bit or its independent activation bit is open. The
point is not abstract monotonicity: we prove the exact bond-pivot to
activation-pivot statement and feed the resulting one-coordinate modification
to the finite inhomogeneous transport theorem.

The general Aizenman--Grimmett strict critical-point theorem is not asserted.
In particular, this one-edge gadget does not supply the annular rewiring lemma
needed for arbitrary bounded-range enhancements on arbitrary quasi-transitive
graphs.
-/

open Set
open scoped BigOperators

namespace FK.AGGadget

open FK.EssentialEnhancement FK.AGPeeling

universe u

/-- The enhanced edge is open precisely when its bond or activation bit is
open. Bond and activation coordinates remain distinct in the joint law. -/
def enhancedConfig {E : Type u} (χ : JointConfig E E) : E → Bool :=
  fun e => χ (Sum.inl e) || χ (Sum.inr e)

@[simp] theorem enhancedConfig_apply {E : Type u} (χ : JointConfig E E) (e : E) :
    enhancedConfig χ e = (χ (Sum.inl e) || χ (Sum.inr e)) := rfl

/-- Pull back an event on enhanced bonds to the joint bond/activation state. -/
def enhancedEvent {E : Type u} (B : Set (E → Bool)) : Set (JointConfig E E) :=
  enhancedConfig ⁻¹' B

lemma enhancedConfig_mono {E : Type u} {χ ξ : JointConfig E E} (h : χ ≤ ξ) :
    enhancedConfig χ ≤ enhancedConfig ξ := by
  intro e
  have hor : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by decide
  exact hor _ _ _ _ (h (Sum.inl e)) (h (Sum.inr e))

lemma isUpperSet_enhancedEvent {E : Type u} {B : Set (E → Bool)}
    (hB : IsUpperSet B) : IsUpperSet (enhancedEvent (E := E) B) := by
  intro χ ξ hχξ hχ
  exact hB (enhancedConfig_mono hχξ) hχ

/-- The only local modification used by the elementary edge gadget: close the
bond bit at `e`, leaving every activation and every other bond unchanged. -/
noncomputable def bondToActivation {E : Type u} (e : E) :
    JointConfig E E → JointConfig E E :=
  fun χ => forceEdge χ (Sum.inl e) false

theorem bondToActivation_isLocalModification {E : Type u} [DecidableEq E]
    (e : E) : IsLocalModification {Sum.inl e} (bondToActivation e) := by
  intro χ x hx
  have hxe : x ≠ Sum.inl e := by simpa using hx
  exact forceEdge_of_ne _ hxe false

/-- If the activation at an edge were already open, its bond could not be
pivotal for the enhanced event: opening and closing that bond would give the
same enhanced configuration. -/
lemma activation_eq_false_of_edgePivotal {E : Type u} {B : Set (E → Bool)}
    {e : E} {χ : JointConfig E E}
    (hpiv : EdgePivotal (enhancedEvent B) e χ) : χ (Sum.inr e) = false := by
  classical
  cases ha : χ (Sum.inr e)
  · rfl
  · exfalso
    apply hpiv.2
    have hmem := hpiv.1
    change enhancedConfig (forceEdge χ (Sum.inl e) false) ∈ B
    change enhancedConfig (forceEdge χ (Sum.inl e) true) ∈ B at hmem
    have heq : enhancedConfig (forceEdge χ (Sum.inl e) false) =
        enhancedConfig (forceEdge χ (Sum.inl e) true) := by
      funext f
      by_cases hf : f = e
      · subst f
        simp [enhancedConfig, ha]
      · simp [enhancedConfig_apply, forceEdge, hf]
    rwa [heq]

/-- After closing the bond, forcing the activation at `e` to `b` gives exactly
the enhanced configuration obtained by forcing the original bond to `b`.
Pivotality forces the old activation to be closed, which is the case needed
below. -/
lemma enhancedConfig_bondToActivation_force {E : Type u}
    (χ : JointConfig E E) (e : E) (b : Bool) (ha : χ (Sum.inr e) = false) :
    enhancedConfig (forceEdge (bondToActivation e χ) (Sum.inr e) b) =
      enhancedConfig (forceEdge χ (Sum.inl e) b) := by
  classical
  funext f
  by_cases hf : f = e
  · subst f
    cases b <;> simp [enhancedConfig, bondToActivation, ha]
  · simp [enhancedConfig_apply, bondToActivation, forceEdge, hf]

/-- **Exact local pivot semantics of the one-edge enhancement gadget.**  A
bond pivot at `e` becomes an activation pivot at the same edge after only the
bond bit at `e` is closed.  This is a statement about the genuine enhanced
event, not the activation-independent `bondEvent` from `AGPeeling`. -/
theorem activationPivotal_bondToActivation {E : Type u} {B : Set (E → Bool)}
    {e : E} {χ : JointConfig E E}
    (hpiv : EdgePivotal (enhancedEvent B) e χ) :
    ActivationPivotal (enhancedEvent B) e (bondToActivation e χ) := by
  have ha := activation_eq_false_of_edgePivotal hpiv
  constructor
  · change enhancedConfig (forceEdge (bondToActivation e χ) (Sum.inr e) true) ∈ B
    rw [enhancedConfig_bondToActivation_force χ e true ha]
    exact hpiv.1
  · change enhancedConfig (forceEdge (bondToActivation e χ) (Sum.inr e) false) ∉ B
    rw [enhancedConfig_bondToActivation_force χ e false ha]
    exact hpiv.2

/-- The actual enhanced one-arm event on a simple graph.  In contrast with
`jointArmEvent`, activations can be pivotal for this event. -/
def enhancedArmEvent {V : Type*} (G : SimpleGraph V) (o : V) (n : ℕ) :
    Set (JointConfig G.edgeSet G.edgeSet) :=
  enhancedEvent (CurvatureVariance.Infra.Percolation.armEvent G o n)

lemma isUpperSet_enhancedArmEvent {V : Type*} (G : SimpleGraph V) (o : V) (n : ℕ) :
    IsUpperSet (enhancedArmEvent G o n) :=
  isUpperSet_enhancedEvent
    (CurvatureVariance.Infra.Percolation.isUpperSet_armEvent o n)

open FK.Finite.Comparison

/-- **Finite inhomogeneous bond/activation pivot comparison.**  The bond and
activation coordinates have their own arbitrary normalized Bernoulli laws.
Only one coordinate, `inl e`, is changed, so the general transport bound
specializes to the explicit constants `δ` and `2`. -/
theorem edgePivotal_event_mul_le {E : Type u} [Fintype E] [DecidableEq E]
    (bondRate activationRate : E → ℝ)
    (hbondRate : ∀ e, bondRate e ∈ Icc (0 : ℝ) 1)
    (hactivationRate : ∀ e, activationRate e ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (boolLaw (bondRate e) (hbondRate e)).mass b)
    (hactivation : ∀ e b,
      δ ≤ (boolLaw (activationRate e) (hactivationRate e)).mass b)
    (B : Set (E → Bool)) (e : E) :
    let μ := OpenPath.FinProb.pi (Sum.elim
      (fun f => boolLaw (bondRate f) (hbondRate f))
      (fun f => boolLaw (activationRate f) (hactivationRate f)))
    δ * μ.event {χ | EdgePivotal (enhancedEvent B) e χ} ≤
      2 * μ.event {χ | ActivationPivotal (enhancedEvent B) e χ} := by
  classical
  dsimp only
  have h := local_joint_edgePivotal_event_mul_le
    (fun f => boolLaw (bondRate f) (hbondRate f))
    (fun f => boolLaw (activationRate f) (hactivationRate f))
    {Sum.inl e} δ hδ hbond hactivation (bondToActivation e)
    (bondToActivation_isLocalModification e) (enhancedEvent B) e [e]
    (fun χ hpiv => ⟨e, by simp, activationPivotal_bondToActivation hpiv⟩)
  simpa using h

/-- Summing the local comparison gives the finite expected-pivot-count
inequality, with the same exact inhomogeneous joint law on every summand. -/
theorem sum_edgePivotal_event_mul_le {E : Type u} [Fintype E] [DecidableEq E]
    (bondRate activationRate : E → ℝ)
    (hbondRate : ∀ e, bondRate e ∈ Icc (0 : ℝ) 1)
    (hactivationRate : ∀ e, activationRate e ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (boolLaw (bondRate e) (hbondRate e)).mass b)
    (hactivation : ∀ e b,
      δ ≤ (boolLaw (activationRate e) (hactivationRate e)).mass b)
    (B : Set (E → Bool)) :
    let μ := OpenPath.FinProb.pi (Sum.elim
      (fun f => boolLaw (bondRate f) (hbondRate f))
      (fun f => boolLaw (activationRate f) (hactivationRate f)))
    δ * ∑ e, μ.event {χ | EdgePivotal (enhancedEvent B) e χ} ≤
      2 * ∑ e, μ.event {χ | ActivationPivotal (enhancedEvent B) e χ} := by
  classical
  dsimp only
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  exact edgePivotal_event_mul_le bondRate activationRate hbondRate hactivationRate
    δ hδ hbond hactivation B e

/-- The probability that at least one of two independent bits is open. -/
def orRate (p s : ℝ) : ℝ := p + (1 - p) * s

lemma orRate_mem_Icc {p s : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : orRate p s ∈ Icc (0 : ℝ) 1 := by
  rcases hp with ⟨hp0, hp1⟩
  rcases hs with ⟨hs0, hs1⟩
  constructor <;> simp only [orRate] <;> nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hs0]

/-- A pair of independent bond/activation bits has the exact OR-marginal
`p + (1-p)s`. -/
lemma prod_boolLaw_map_or {p s : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (OpenPath.FinProb.prod (boolLaw p hp) (boolLaw s hs)).map
      (fun x : Bool × Bool => x.1 || x.2) = boolLaw (orRate p s) (orRate_mem_Icc hp hs) := by
  apply OpenPath.FinProb.ext
  intro b
  cases b <;>
    simp [OpenPath.FinProb.mass_map, OpenPath.FinProb.prod, boolLaw,
      Fintype.sum_prod_type, orRate] <;> ring

/-- Equivalence between disjoint bond/activation coordinates and independent
pairs indexed by the same edge. -/
def jointPairedEquiv {E : Type u} : JointConfig E E ≃ (E → Bool × Bool) where
  toFun χ e := (χ (Sum.inl e), χ (Sum.inr e))
  invFun ω := Sum.elim (fun e => (ω e).1) (fun e => (ω e).2)
  left_inv χ := by funext x; cases x <;> rfl
  right_inv ω := by
    funext e
    change ((ω e).1, (ω e).2) = ω e
    exact Prod.ext rfl rfl

/-- The normalized joint law used in the pivot comparison, named separately
so its enhanced marginal can be computed. -/
noncomputable def jointLaw {E : Type u} [Fintype E] [DecidableEq E]
    (bondRate activationRate : E → ℝ)
    (hbondRate : ∀ e, bondRate e ∈ Icc (0 : ℝ) 1)
    (hactivationRate : ∀ e, activationRate e ∈ Icc (0 : ℝ) 1) :
    OpenPath.FinProb (JointConfig E E) :=
  OpenPath.FinProb.pi (Sum.elim
    (fun e => boolLaw (bondRate e) (hbondRate e))
    (fun e => boolLaw (activationRate e) (hactivationRate e)))

/-- The same joint law on edge-indexed independent pairs. -/
noncomputable def pairedLaw {E : Type u} [Fintype E] [DecidableEq E]
    (bondRate activationRate : E → ℝ)
    (hbondRate : ∀ e, bondRate e ∈ Icc (0 : ℝ) 1)
    (hactivationRate : ∀ e, activationRate e ∈ Icc (0 : ℝ) 1) :
    OpenPath.FinProb (E → Bool × Bool) :=
  OpenPath.FinProb.pi (fun e => OpenPath.FinProb.prod
    (boolLaw (bondRate e) (hbondRate e))
    (boolLaw (activationRate e) (hactivationRate e)))

lemma jointLaw_map_paired {E : Type u} [Fintype E] [DecidableEq E]
    (bondRate activationRate : E → ℝ)
    (hbondRate : ∀ e, bondRate e ∈ Icc (0 : ℝ) 1)
    (hactivationRate : ∀ e, activationRate e ∈ Icc (0 : ℝ) 1) :
    (jointLaw bondRate activationRate hbondRate hactivationRate).map
      jointPairedEquiv = pairedLaw bondRate activationRate hbondRate hactivationRate := by
  apply OpenPath.FinProb.ext
  intro ω
  rw [OpenPath.FinProb.mass_map_equiv]
  simp only [jointLaw, pairedLaw, OpenPath.FinProb.pi_mass,
    Fintype.prod_sum_type, OpenPath.FinProb.prod_mass, jointPairedEquiv,
    Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.prod_mul_distrib]

/-- **Exact enhanced Bernoulli marginal.**  Mapping the actual joint product
law by `enhancedConfig` gives independent Bernoulli bonds with the respective
rates `pₑ + (1-pₑ)sₑ`; no abstract or unnormalized product model is used. -/
theorem enhancedConfig_jointLaw {E : Type u} [Fintype E] [DecidableEq E]
    (bondRate activationRate : E → ℝ)
    (hbondRate : ∀ e, bondRate e ∈ Icc (0 : ℝ) 1)
    (hactivationRate : ∀ e, activationRate e ∈ Icc (0 : ℝ) 1) :
    (jointLaw bondRate activationRate hbondRate hactivationRate).map enhancedConfig =
      boolProduct (fun e => orRate (bondRate e) (activationRate e))
        (fun e => orRate_mem_Icc (hbondRate e) (hactivationRate e)) := by
  calc
    (jointLaw bondRate activationRate hbondRate hactivationRate).map enhancedConfig =
        ((jointLaw bondRate activationRate hbondRate hactivationRate).map
          jointPairedEquiv).map (fun ω e => (ω e).1 || (ω e).2) := by
      rw [GlauberCoupling.map_map]
      rfl
    _ = (pairedLaw bondRate activationRate hbondRate hactivationRate).map
        (fun ω e => (ω e).1 || (ω e).2) := by rw [jointLaw_map_paired]
    _ = boolProduct (fun e => orRate (bondRate e) (activationRate e))
        (fun e => orRate_mem_Icc (hbondRate e) (hactivationRate e)) := by
      unfold pairedLaw FK.Finite.Comparison.boolProduct
      change (OpenPath.FinProb.pi (fun e => OpenPath.FinProb.prod
        (boolLaw (bondRate e) (hbondRate e))
        (boolLaw (activationRate e) (hactivationRate e)))).map
          (fun ω e => (fun x : Bool × Bool => x.1 || x.2) (ω e)) = _
      refine (OpenPath.FinProb.pi_map
        (fun e : E => OpenPath.FinProb.prod
          (boolLaw (bondRate e) (hbondRate e))
          (boolLaw (activationRate e) (hactivationRate e)))
        (fun (_ : E) (x : Bool × Bool) => x.1 || x.2)).trans ?_
      congr 1
      funext e
      exact prod_boolLaw_map_or (hbondRate e) (hactivationRate e)

/-- Every enhanced event probability is therefore the probability of the
original event under the exact enhanced inhomogeneous Bernoulli product. -/
theorem enhancedEvent_jointLaw {E : Type u} [Fintype E] [DecidableEq E]
    (bondRate activationRate : E → ℝ)
    (hbondRate : ∀ e, bondRate e ∈ Icc (0 : ℝ) 1)
    (hactivationRate : ∀ e, activationRate e ∈ Icc (0 : ℝ) 1)
    (B : Set (E → Bool)) :
    (jointLaw bondRate activationRate hbondRate hactivationRate).event
      (enhancedEvent B) =
        (boolProduct (fun e => orRate (bondRate e) (activationRate e))
          (fun e => orRate_mem_Icc (hbondRate e) (hactivationRate e))).event B := by
  change (jointLaw bondRate activationRate hbondRate hactivationRate).event
    (enhancedConfig ⁻¹' B) = _
  rw [OpenPath.FinProb.event_preimage_map, enhancedConfig_jointLaw]

/-- Essentiality of the explicit stochastic enhancement, expressed in exactly
the activation-pivot language used by the finite transport theorem. -/
def EnhancedEssential {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : Prop :=
  ∃ χ, ActivationPivotal
    (enhancedEvent {ω | HasOpenDoubleRay (G := G) ω}) e χ

/-- The joint state supported on the de-activated configuration of a double
ray, with the distinguished bond initially closed. -/
noncomputable def rayJoint {V : Type*} {G : SimpleGraph V}
    (r : DoubleRay G) (e : G.edgeSet) : JointConfig G.edgeSet G.edgeSet :=
  Sum.elim (forceEdge r.configuration e false) (fun _ => false)

@[simp] lemma rayJoint_inl {V : Type*} {G : SimpleGraph V}
    (r : DoubleRay G) (e f : G.edgeSet) :
    rayJoint r e (Sum.inl f) = forceEdge r.configuration e false f := rfl

@[simp] lemma rayJoint_inr {V : Type*} {G : SimpleGraph V}
    (r : DoubleRay G) (e f : G.edgeSet) :
    rayJoint r e (Sum.inr f) = false := rfl

lemma enhancedConfig_rayJoint_off {V : Type*} {G : SimpleGraph V}
    (r : DoubleRay G) (e : G.edgeSet) :
    enhancedConfig (forceEdge (rayJoint r e) (Sum.inr e) false) =
      forceEdge r.configuration e false := by
  classical
  funext f
  have hne : (Sum.inl f : G.edgeSet ⊕ G.edgeSet) ≠ Sum.inr e := by simp
  rw [enhancedConfig_apply, forceEdge_of_ne _ hne, rayJoint_inl]
  by_cases hf : f = e
  · subst f
    simp only [forceEdge_same, Bool.or_false]
  · have hne' : (Sum.inr f : G.edgeSet ⊕ G.edgeSet) ≠ Sum.inr e := by simp [hf]
    rw [forceEdge_of_ne _ hne', rayJoint_inr, Bool.or_false]

lemma enhancedConfig_rayJoint_on {V : Type*} {G : SimpleGraph V}
    (r : DoubleRay G) (e : G.edgeSet) :
    enhancedConfig (forceEdge (rayJoint r e) (Sum.inr e) true) =
      forceEdge r.configuration e true := by
  classical
  funext f
  have hne : (Sum.inl f : G.edgeSet ⊕ G.edgeSet) ≠ Sum.inr e := by simp
  rw [enhancedConfig_apply, forceEdge_of_ne _ hne, rayJoint_inl]
  by_cases hf : f = e
  · subst f
    simp only [forceEdge_same, Bool.false_or]
  · have hne' : (Sum.inr f : G.edgeSet ⊕ G.edgeSet) ≠ Sum.inr e := by simp [hf]
    rw [forceEdge_of_ne _ hne', rayJoint_inr, Bool.or_false,
      forceEdge_of_ne _ hf false]
    exact (forceEdge_of_ne _ hf true).symm

/-- **Existence of an essential activation.**  Every edge on a genuine simple
double ray gives an explicit joint configuration for which its activation is
pivotal for the existence of an open enhanced double ray. -/
theorem enhancedEssential_of_onDoubleRay {V : Type*} {G : SimpleGraph V}
    {e : G.edgeSet} (he : OnDoubleRay e) : EnhancedEssential G e := by
  obtain ⟨r, k, hk⟩ := he
  refine ⟨rayJoint r e, ?_, ?_⟩
  · change HasOpenDoubleRay
      (enhancedConfig (forceEdge (rayJoint r e) (Sum.inr e) true))
    rw [enhancedConfig_rayJoint_on]
    exact hasOpenDoubleRay_update_configuration_true r hk
  · change ¬ HasOpenDoubleRay
      (enhancedConfig (forceEdge (rayJoint r e) (Sum.inr e) false))
    rw [enhancedConfig_rayJoint_off]
    exact not_hasOpenDoubleRay_update_configuration_false r hk

/-- A maximal disjoint family of devices gives a bounded-distance set of
actually essential activations.  The local cover and diameter assumptions are
on edge sets in the original simple graph; no abstract `BoundedDistance`
assertion is assumed as an input. -/
theorem exists_boundedDistance_enhancedEssential
    {V : Type*} {Device : Type*} (G : SimpleGraph V)
    (support : Device → Set G.edgeSet) (D : Set Device)
    (pivot : Device → G.edgeSet) (hpivot : ∀ d, pivot d ∈ support d)
    (hpivotalRay : ∀ d, OnDoubleRay (G := G) (pivot d))
    (edgeDist : G.edgeSet → G.edgeSet → ℕ)
    (htriangle : ∀ a b c, edgeDist a c ≤ edgeDist a b + edgeDist b c)
    (K R : ℕ)
    (hlocal : ∀ e, ∃ d ∈ D, ∀ f ∈ support d, edgeDist e f ≤ K)
    (hdiam : ∀ d ∈ D, ∀ f ∈ support d, edgeDist f (pivot d) ≤ R) :
    ∃ S : Set G.edgeSet, FK.Theorem14.BoundedDistance edgeDist S ∧
      ∀ e ∈ S, EnhancedEssential G e := by
  obtain ⟨M, hMD, hMpair, hMaux, hMmeet, hMdense⟩ :=
    FK.DevicePacking.exists_uniform_device_packing support D pivot hpivot
      edgeDist htriangle K R hlocal hdiam
  refine ⟨pivot '' M, ⟨K + R, hMdense⟩, ?_⟩
  rintro e ⟨d, hd, rfl⟩
  exact enhancedEssential_of_onDoubleRay (hpivotalRay d)

/-- The bounded-distance conclusion specialized to the genuine graph metric on
edges: distance in the line graph of `G`.  Thus no choice of a zero or otherwise
degenerate auxiliary metric can make the density conclusion vacuous. -/
theorem exists_lineGraphBoundedDistance_enhancedEssential
    {V : Type*} {Device : Type*} (G : SimpleGraph V) (hconn : G.lineGraph.Connected)
    (support : Device → Set G.edgeSet) (D : Set Device)
    (pivot : Device → G.edgeSet) (hpivot : ∀ d, pivot d ∈ support d)
    (hpivotalRay : ∀ d, OnDoubleRay (G := G) (pivot d))
    (K R : ℕ)
    (hlocal : ∀ e, ∃ d ∈ D, ∀ f ∈ support d, G.lineGraph.dist e f ≤ K)
    (hdiam : ∀ d ∈ D, ∀ f ∈ support d, G.lineGraph.dist f (pivot d) ≤ R) :
    ∃ S : Set G.edgeSet, FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      ∀ e ∈ S, EnhancedEssential G e := by
  exact exists_boundedDistance_enhancedEssential G support D pivot hpivot hpivotalRay
    G.lineGraph.dist (fun _ _ _ => hconn.dist_triangle) K R hlocal hdiam

end FK.AGGadget
