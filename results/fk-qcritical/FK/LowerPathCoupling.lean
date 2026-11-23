import FK.LowerPathStationarity
import FK.LowerCutsetComparison

/-!
# Ordered joint dynamics for the lower open-path comparison

The lower path-enhanced product chain and the actual FK chain are coupled by
one common clock and one common ordered bit update. Both chains start at the
all-closed configuration, so no initial joint law or joint limit is assumed.
-/

noncomputable section

open scoped Classical BigOperators
open Set Filter
open FK.Finite FK.Finite.Conditional Glauber

namespace OpenPath.LowerPathCoupling

open Glauber.FKBridge

/-- Connection without a distinguished edge is monotone in the other edges. -/
lemma endpointsConnectedWithout_mono
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (e : G.Edge)
    {ω η : G.Edge → Bool} (h : ω ≤ η) :
    endpointsConnectedWithout G ξ e ω → endpointsConnectedWithout G ξ e η := by
  intro hconn
  unfold endpointsConnectedWithout at hconn ⊢
  apply hconn.mono
  apply G.connectionGraph_mono
  intro a
  by_cases ha : a = e
  · subst a
    simp [FK.FiniteFiber.withEdge]
  · simpa [FK.FiniteFiber.withEdge_off ha] using h a

/-- The Bool conversion of the lower off-configuration lies below the FK
off-configuration whenever the two full configurations are ordered. -/
lemma configToBool_pathOff_le_offConfiguration
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (e : G.Edge)
    {y : Config G.Edge} {x : G.Edge → Bool}
    (hyx : y ≤ configOfBool x) :
    configToBool (pathOffConfiguration e (fun f => y f.1)) ≤
      offConfiguration G ξ e (fun f => x f.1) := by
  have hcb : configToBool (configOfBool x) = x := by
    funext a
    exact bitBoolEquiv.right_inv (x a)
  have h' : configToBool y ≤ x := by
    rw [← hcb]
    exact configToBool_le_iff.mpr hyx
  intro f
  by_cases hf : f = e
  · subst f
    simp [configToBool, bitToBool, pathOffConfiguration, configSplit,
      Equiv.funSplitAt_symm_apply]
  · change bitToBool (pathOffConfiguration e (fun f => y f.1) f) ≤ _
    rw [pathOffConfiguration_apply_of_ne e f _ hf]
    have hoff : offConfiguration G ξ e (fun f => x f.1) f = x f := by
      simp [offConfiguration, configSplit, Equiv.funSplitAt_symm_apply, hf]
    rw [hoff]
    exact h' f

/-- At an ordered input state, the path-enhanced lower conditional rate is at
most the actual FK conditional rate. -/
lemma lowerPathRate_le_openRate
    (G : LabelledMultigraph) {q p : NNReal} (ξ : G.BoundaryPartition)
    (enhanced : Finset G.Edge) {p' : ℝ} (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) {y : Config G.Edge} {x : G.Edge → Bool}
    (hyx : y ≤ configOfBool x) :
    pathProductRate enhanced (p : ℝ) p' Γ e (fun f => y f.1) ≤
      openRate G (q := q) (p := p) ξ e (fun f => x f.1) := by
  classical
  by_cases he : e ∈ enhanced
  · by_cases hpth : SomePathOpen (Γ e)
      (pathOffConfiguration e (fun f => y f.1))
    · have hc₀ := hpath e he hpth
      have hc : endpointsConnectedWithout G ξ e
          (offConfiguration G ξ e (fun f => x f.1)) :=
        endpointsConnectedWithout_mono G ξ e
          (configToBool_pathOff_le_offConfiguration G ξ e hyx) hc₀
      simp [pathProductRate, openRate, he, hpth, hc]
    · simp [pathProductRate, openRate, he, hpth]
      split_ifs <;> assumption
  · simp [pathProductRate, openRate, he]
    split_ifs <;> assumption

/-- The two actual one-edge rates, packaged to shorten the coupling definitions. -/
noncomputable def lowerPathLocalRate
    (G : LabelledMultigraph) (p : NNReal) (enhanced : Finset G.Edge)
    (p' : ℝ) (Γ : G.Edge → Set (Finset G.Edge)) (e : G.Edge) (y : Config G.Edge) : ℝ :=
  pathProductRate enhanced (p : ℝ) p' Γ e (fun f => y f.1)

noncomputable def lowerPathLocalFKRate
    (G : LabelledMultigraph) (q p : NNReal) (ξ : G.BoundaryPartition)
    (e : G.Edge) (x : G.Edge → Bool) : ℝ :=
  openRate G (q := q) (p := p) ξ e (fun f => x f.1)

lemma lowerPathLocalRate_mem_Icc
    (G : LabelledMultigraph) {p : NNReal} (hp : p ≤ 1)
    (enhanced : Finset G.Edge) {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1)
    (Γ : G.Edge → Set (Finset G.Edge)) (e : G.Edge) (y : Config G.Edge) :
    lowerPathLocalRate G p enhanced p' Γ e y ∈ Icc (0 : ℝ) 1 := by
  exact pathProductRate_mem_Icc enhanced
    ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ e (fun f => y f.1)

lemma lowerPathLocalFKRate_mem_Icc
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (e : G.Edge) (x : G.Edge → Bool) :
    lowerPathLocalFKRate G q p ξ e x ∈ Icc (0 : ℝ) 1 := by
  exact openRate_mem_Icc G hq hp ξ e (fun f => x f.1)

/-- Ordered coupling of the two bit laws. Away from ordered inputs an
independent coupling is used, solely to make both marginals globally exact. -/
noncomputable def lowerPathLocalLaw
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) (y : Config G.Edge) (x : G.Edge → Bool) : FinProb (Bit × Bit) := by
  classical
  exact if hyx : y ≤ configOfBool x then
    coupledPair (lowerPathLocalRate G p enhanced p' Γ e y)
      (lowerPathLocalFKRate G q p ξ e x)
      (lowerPathLocalRate_mem_Icc G hp enhanced hp' Γ e y).1
      (by
        simpa [lowerPathLocalRate, lowerPathLocalFKRate] using
          (lowerPathRate_le_openRate G ξ enhanced h hpprime Γ hpath e hyx))
      (lowerPathLocalFKRate_mem_Icc G hq hp ξ e x).2
  else
    (bitLaw (lowerPathLocalRate G p enhanced p' Γ e y)
      (lowerPathLocalRate_mem_Icc G hp enhanced hp' Γ e y)).prod
    (bitLaw (lowerPathLocalFKRate G q p ξ e x)
      (lowerPathLocalFKRate_mem_Icc G hq hp ξ e x))

lemma lowerPathLocalLaw_map_fst
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) (y : Config G.Edge) (x : G.Edge → Bool) :
    (lowerPathLocalLaw G hq hp ξ enhanced hp' h hpprime Γ hpath e y x).map Prod.fst =
      bitLaw (lowerPathLocalRate G p enhanced p' Γ e y)
        (lowerPathLocalRate_mem_Icc G hp enhanced hp' Γ e y) := by
  classical
  unfold lowerPathLocalLaw
  split_ifs with hyx
  · exact coupledPair_fst _ _ _ _ _
  · exact FinProb.prod_map_fst _ _

lemma lowerPathLocalLaw_map_snd
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) (y : Config G.Edge) (x : G.Edge → Bool) :
    (lowerPathLocalLaw G hq hp ξ enhanced hp' h hpprime Γ hpath e y x).map Prod.snd =
      bitLaw (lowerPathLocalFKRate G q p ξ e x)
        (lowerPathLocalFKRate_mem_Icc G hq hp ξ e x) := by
  classical
  unfold lowerPathLocalLaw
  split_ifs with hyx
  · exact coupledPair_snd _ _ _ _ _
  · exact FinProb.prod_map_snd _ _

lemma lowerPathLocalLaw_ordered
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) {y : Config G.Edge} {x : G.Edge → Bool}
    (hyx : y ≤ configOfBool x) {b : Bit × Bit}
    (hb : (lowerPathLocalLaw G hq hp ξ enhanced hp' h hpprime Γ hpath e y x).mass b ≠ 0) :
    b.1 ≤ b.2 := by
  classical
  unfold lowerPathLocalLaw at hb
  rw [dif_pos hyx] at hb
  exact coupledPair_ordered _ _ _ _ _ hb

/-- Conversion of the bit-Bernoulli law to the Boolean FK convention. -/
lemma bitLaw_map_bitToBool {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (bitLaw r hr).map bitToBool = Glauber.FKBridge.boolLaw r hr := by
  apply FinProb.ext
  intro b
  cases b <;>
    simp [FinProb.mass_map, bitLaw, Glauber.FKBridge.boolLaw, bitToBool,
      Fin.sum_univ_two]

end OpenPath.LowerPathCoupling


namespace OpenPath.LowerPathCoupling

open Glauber.FKBridge

/-- Lower path configuration together with the actual Boolean FK configuration. -/
abbrev JointState (G : LabelledMultigraph) := Config G.Edge × (G.Edge → Bool)

/-- The order invariant of the coupled dynamics. -/
def JointOrdered {G : LabelledMultigraph} (s : JointState G) : Prop :=
  s.1 ≤ configOfBool s.2

/-- One common ordered update at one edge. -/
noncomputable def lowerPathJointEdgeUpdate
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) (s : JointState G) : FinProb (JointState G) :=
  (lowerPathLocalLaw G hq hp ξ enhanced hp' h hpprime Γ hpath e s.1 s.2).map
    (fun b => (Function.update s.1 e b.1,
      Function.update s.2 e (bitToBool b.2)))

/-- The first marginal is exactly the path-product heat bath. -/
lemma lowerPathJointEdgeUpdate_map_fst
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) (s : JointState G) :
    (lowerPathJointEdgeUpdate G hq hp ξ enhanced hp' h hpprime Γ hpath e s).map
      Prod.fst = edgeUpdate (pathProductConditionals enhanced
        ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ) e s.1 := by
  classical
  unfold lowerPathJointEdgeUpdate
  rw [GlauberCoupling.map_map]
  change (lowerPathLocalLaw G hq hp ξ enhanced hp' h hpprime Γ hpath e s.1 s.2).map
    (Function.update s.1 e ∘ Prod.fst) = _
  rw [← GlauberCoupling.map_map, lowerPathLocalLaw_map_fst]
  exact (edgeUpdate_eq_map (pathProductConditionals enhanced
    ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ) e s.1).symm

/-- The second marginal is exactly the actual FK heat bath. -/
lemma lowerPathJointEdgeUpdate_map_snd
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) (s : JointState G) :
    (lowerPathJointEdgeUpdate G hq hp ξ enhanced hp' h hpprime Γ hpath e s).map
      Prod.snd = edgeUpdate (edgeConditionals G hq hp ξ) e s.2 := by
  classical
  unfold lowerPathJointEdgeUpdate
  rw [GlauberCoupling.map_map]
  change (lowerPathLocalLaw G hq hp ξ enhanced hp' h hpprime Γ hpath e s.1 s.2).map
    (Function.update s.2 e ∘ (bitToBool ∘ Prod.snd)) = _
  rw [← GlauberCoupling.map_map, ← GlauberCoupling.map_map,
    lowerPathLocalLaw_map_snd, bitLaw_map_bitToBool]
  exact (edgeUpdate_eq_map (edgeConditionals G hq hp ξ) e s.2).symm

/-- One common update preserves the lower/FK order. -/
lemma lowerPathJointEdgeUpdate_ordered
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (e : G.Edge) {s : JointState G} (hs : JointOrdered s)
    {u : JointState G}
    (hu : (lowerPathJointEdgeUpdate G hq hp ξ enhanced hp' h hpprime Γ hpath
      e s).mass u ≠ 0) : JointOrdered u := by
  classical
  obtain ⟨b, hb, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero hu
  have hb' : b.1 ≤ b.2 :=
    lowerPathLocalLaw_ordered G hq hp ξ enhanced hp' h hpprime Γ hpath e hs hb
  change Function.update s.1 e b.1 ≤
    configOfBool (Function.update s.2 e (bitToBool b.2))
  intro f
  by_cases hf : f = e
  · subst f
    simp only [Function.update_self]
    change b.1 ≤ (configOfBool (Function.update s.2 e (bitToBool b.2))) e
    simp only [configOfBool, Function.update_self]
    rw [show boolToBit (bitToBool b.2) = b.2 from bitBoolEquiv.left_inv b.2]
    exact hb'
  · simp only [Function.update_of_ne hf]
    change s.1 f ≤ (configOfBool (Function.update s.2 e (bitToBool b.2))) f
    simp only [configOfBool, Function.update_of_ne hf]
    exact hs f

/-- Coupled sequential modified-block update. -/
noncomputable def lowerPathJointBlockUpdate
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (auxiliary : List G.Edge) (e : G.Edge) : JointState G → FinProb (JointState G) :=
  sweep ((blockCoordinates enhanced auxiliary e).map
    (lowerPathJointEdgeUpdate G hq hp ξ enhanced hp' h hpprime Γ hpath))

/-- Coupled shared-clock modified jump. -/
noncomputable def lowerPathJointJump
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) :
    JointState G → FinProb (JointState G) :=
  mixture ρ (lowerPathJointBlockUpdate G hq hp ξ enhanced hp' h hpprime Γ hpath auxiliary)

/-- Both coordinates start at the all-closed configuration. -/
noncomputable def lowerPathJointInitial (G : LabelledMultigraph) : FinProb (JointState G) :=
  FinProb.dirac ((fun _ => 0), (fun _ => false))

/-- Exact finite-time laws of the coupled chains. -/
noncomputable def lowerPathJointLaw
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) : ℕ → FinProb (JointState G) :=
  GlauberCoupling.iterateLaw (lowerPathJointInitial G)
    (lowerPathJointJump G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary)

/-- Projection of a coupled block onto the lower path-product block. -/
lemma lowerPathJointBlockUpdate_map_fst
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (auxiliary : List G.Edge) (e : G.Edge) (s : JointState G) :
    (lowerPathJointBlockUpdate G hq hp ξ enhanced hp' h hpprime Γ hpath
      auxiliary e s).map Prod.fst = blockUpdate (pathProductConditionals enhanced
        ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ) enhanced auxiliary e s.1 := by
  unfold lowerPathJointBlockUpdate blockUpdate
  exact Glauber.map_sweep_kernel Prod.fst _ _
    (lowerPathJointEdgeUpdate_map_fst G hq hp ξ enhanced hp' h hpprime Γ hpath) _ s

/-- Projection of a coupled block onto the actual FK block. -/
lemma lowerPathJointBlockUpdate_map_snd
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (auxiliary : List G.Edge) (e : G.Edge) (s : JointState G) :
    (lowerPathJointBlockUpdate G hq hp ξ enhanced hp' h hpprime Γ hpath
      auxiliary e s).map Prod.snd = blockUpdate (edgeConditionals G hq hp ξ)
        enhanced auxiliary e s.2 := by
  unfold lowerPathJointBlockUpdate blockUpdate
  exact Glauber.map_sweep_kernel Prod.snd _ _
    (lowerPathJointEdgeUpdate_map_snd G hq hp ξ enhanced hp' h hpprime Γ hpath) _ s

/-- Projection of a coupled jump onto the lower path-product jump. -/
lemma lowerPathJointJump_map_fst
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) (s : JointState G) :
    (lowerPathJointJump G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary s).map
      Prod.fst = pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
        ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ auxiliary s.1 := by
  unfold lowerPathJointJump pathProductKernel modifiedJump
  exact Glauber.map_mixture Prod.fst ρ _ _
    (lowerPathJointBlockUpdate_map_fst G hq hp ξ enhanced hp' h hpprime Γ hpath auxiliary) s

/-- Projection of a coupled jump onto the actual FK jump. -/
lemma lowerPathJointJump_map_snd
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) (s : JointState G) :
    (lowerPathJointJump G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary s).map
      Prod.snd = modifiedJump ρ (edgeConditionals G hq hp ξ) enhanced auxiliary s.2 := by
  unfold lowerPathJointJump modifiedJump
  exact Glauber.map_mixture Prod.snd ρ _ _
    (lowerPathJointBlockUpdate_map_snd G hq hp ξ enhanced hp' h hpprime Γ hpath auxiliary) s

/-- Exact lower path-product marginal at every finite time. -/
lemma lowerPathJointLaw_map_fst
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) (n : ℕ) :
    (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
      Prod.fst = (FinProb.dirac (fun _ : G.Edge => 0)).bind
        (iterate (pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
          ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ auxiliary) n) := by
  have hm := Glauber.map_iterateLaw Prod.fst
    (lowerPathJointJump G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary)
    (pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
      ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ auxiliary)
    (lowerPathJointJump_map_fst G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary)
    (lowerPathJointInitial G) n
  have hinit : (lowerPathJointInitial G).map Prod.fst =
      FinProb.dirac (fun _ : G.Edge => 0) := by
    exact Glauber.map_dirac _ _
  rw [hinit] at hm
  change (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
    Prod.fst = _ at hm
  rw [GlauberCoupling.iterateLaw_eq_bind_iterate] at hm
  exact hm

/-- Exact actual FK marginal at every finite time. -/
lemma lowerPathJointLaw_map_snd
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) (n : ℕ) :
    (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
      Prod.snd = (FinProb.dirac (fun _ : G.Edge => false)).bind
        (iterate (modifiedJump ρ (edgeConditionals G hq hp ξ) enhanced auxiliary) n) := by
  have hm := Glauber.map_iterateLaw Prod.snd
    (lowerPathJointJump G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary)
    (modifiedJump ρ (edgeConditionals G hq hp ξ) enhanced auxiliary)
    (lowerPathJointJump_map_snd G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary)
    (lowerPathJointInitial G) n
  have hinit : (lowerPathJointInitial G).map Prod.snd =
      FinProb.dirac (fun _ : G.Edge => false) := by
    exact Glauber.map_dirac _ _
  rw [hinit] at hm
  change (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
    Prod.snd = _ at hm
  rw [GlauberCoupling.iterateLaw_eq_bind_iterate] at hm
  exact hm

/-- Order propagation through a sequential block. -/
lemma lowerPathJointSweep_ordered
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω)) :
    ∀ (l : List G.Edge) {s : JointState G}, JointOrdered s →
      ∀ {u : JointState G},
        (sweep (l.map (lowerPathJointEdgeUpdate G hq hp ξ enhanced hp' h hpprime Γ
          hpath)) s).mass u ≠ 0 → JointOrdered u := by
  intro l
  induction l with
  | nil =>
      intro s hs u hu
      have hus : u = s := by
        by_contra hne
        simpa [sweep, FinProb.dirac, hne] using hu
      simpa [hus] using hs
  | cons e l ih =>
      intro s hs u hu
      simp only [List.map_cons, sweep] at hu
      unfold Glauber.seq at hu
      obtain ⟨v, hv, hvu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
      exact ih (lowerPathJointEdgeUpdate_ordered G hq hp ξ enhanced hp' h hpprime Γ
        hpath e hs hv) hvu

/-- Order propagation through a common-clock jump. -/
lemma lowerPathJointJump_ordered
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge)
    {s : JointState G} (hs : JointOrdered s) {u : JointState G}
    (hu : (lowerPathJointJump G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary s).mass
      u ≠ 0) : JointOrdered u := by
  unfold lowerPathJointJump lowerPathJointBlockUpdate mixture at hu
  obtain ⟨e, _, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
  exact lowerPathJointSweep_ordered G hq hp ξ enhanced hp' h hpprime Γ hpath _ hs hu

/-- Every supported finite-time joint state is ordered. -/
lemma lowerPathJointLaw_ordered
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) :
    ∀ n u, (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).mass
      u ≠ 0 → JointOrdered u := by
  intro n
  induction n with
  | zero =>
      intro u hu
      change (lowerPathJointInitial G).mass u ≠ 0 at hu
      have hu0 : u = ((fun _ => 0), (fun _ => false)) := by
        by_contra hne
        simpa [lowerPathJointInitial, FinProb.dirac, hne] using hu
      subst u
      intro e
      rfl
  | succ n ih =>
      intro u hu
      change ((lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).bind
        (lowerPathJointJump G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary)).mass
          u ≠ 0 at hu
      obtain ⟨s, hs, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
      exact lowerPathJointJump_ordered G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary
        (ih s hs) hu

end OpenPath.LowerPathCoupling


namespace OpenPath.LowerPathCoupling

open Glauber.FKBridge

/-- The finite-time ordered joint laws on two bit configurations, as required by
`lower_comparison_of_auxiliary_paths_and_orderedDynamics`. -/
noncomputable def lowerPathOrderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) (n : ℕ) :
    FinProb (Config G.Edge × Config G.Edge) :=
  (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
    (fun s => (s.1, configOfBool s.2))

/-- The first marginal of the exported joint law is the lower product chain. -/
lemma lowerPathOrderedDynamics_map_fst
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) (n : ℕ) :
    (lowerPathOrderedDynamics G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
      Prod.fst = (FinProb.dirac (fun _ : G.Edge => 0)).bind
        (iterate (pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
          ⟨p.coe_nonneg, by exact_mod_cast hp⟩ hp' Γ auxiliary) n) := by
  unfold lowerPathOrderedDynamics
  rw [GlauberCoupling.map_map]
  change (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
    Prod.fst = _
  exact lowerPathJointLaw_map_fst G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n

/-- The second marginal is the bit image of the actual FK chain. -/
lemma lowerPathOrderedDynamics_map_snd
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge) (n : ℕ) :
    (lowerPathOrderedDynamics G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
      Prod.snd = ((FinProb.dirac (fun _ : G.Edge => false)).bind
        (iterate (modifiedJump ρ (edgeConditionals G hq hp ξ) enhanced auxiliary) n)).map
          configOfBool := by
  unfold lowerPathOrderedDynamics
  rw [GlauberCoupling.map_map]
  change (lowerPathJointLaw G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).map
    (configOfBool ∘ Prod.snd) = _
  rw [← GlauberCoupling.map_map, lowerPathJointLaw_map_snd]

/-- Every supported state of the exported joint law is ordered. -/
lemma lowerPathOrderedDynamics_ordered
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (auxiliary : List G.Edge)
    (n : ℕ) (a : Config G.Edge × Config G.Edge)
    (ha : (lowerPathOrderedDynamics G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n).mass
      a ≠ 0) : a.1 ≤ a.2 := by
  obtain ⟨s, hs, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ha
  exact lowerPathJointLaw_ordered G hq hp ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n s hs

/-- **Lower open-path comparison, without dynamical hypotheses.** The path
semantics says that a certificate at an enhanced edge connects its endpoints
in the actual wired labelled multigraph. No ordered joint laws, stationarity
equation, joint limit, or initial coupling is assumed. -/
theorem lower_comparison_of_auxiliary_paths
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp0 : 0 < p) (hp1 : p < 1) (ξ : G.BoundaryPartition)
    (enhanced : Finset G.Edge) {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1)
    (hp'0 : 0 < p') (hp'1 : p' < 1) (h : p' ≤ (p : ℝ))
    (hpprime : p' ≤ FK.prime (q : ℝ) (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge)) (hΓ : HasEnhancingPaths enhanced Γ)
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge) (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp1.le) hp' h Γ).map
        configToBool).toMeasure (G.fkPMF hq hp1.le ξ).toMeasure := by
  let joint : ℕ → FinProb (Config G.Edge × Config G.Edge) := fun n =>
    lowerPathOrderedDynamics G hq hp1.le ξ enhanced hp' h hpprime Γ hpath ρ auxiliary n
  have hfst : ∀ n, (joint n).map Prod.fst =
      (FinProb.dirac (fun _ : G.Edge => 0)).bind
        (iterate (pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
          ⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩ hp' Γ auxiliary) n) := by
    exact lowerPathOrderedDynamics_map_fst G hq hp1.le ξ enhanced hp' h hpprime Γ hpath
      ρ auxiliary
  have hsnd : ∀ n, (joint n).map Prod.snd =
      ((FinProb.dirac (fun _ : G.Edge => false)).bind
        (iterate (modifiedJump ρ (edgeConditionals G hq hp1.le ξ) enhanced auxiliary) n)).map
          configOfBool := by
    exact lowerPathOrderedDynamics_map_snd G hq hp1.le ξ enhanced hp' h hpprime Γ hpath
      ρ auxiliary
  have horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2 := by
    exact lowerPathOrderedDynamics_ordered G hq hp1.le ξ enhanced hp' h hpprime Γ hpath
      ρ auxiliary
  exact lower_comparison_of_auxiliary_paths_and_orderedDynamics G hq hp1.le hp0 hp1 ξ
    enhanced hp' hp'0 hp'1 h Γ hΓ.auxiliary
    (FinProb.dirac (fun _ : G.Edge => 0)) (FinProb.dirac (fun _ : G.Edge => false))
    ρ hρ auxiliary haux schedule hschedule joint hfst hsnd horder

/-- Equation-(2) specialization: the disconnected FK conditional parameter is
exactly `FK.prime`, so no separate comparison with that parameter remains. -/
theorem prime_lower_comparison_of_auxiliary_paths
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp0 : 0 < p) (hp1 : p < 1)
    (h : FK.prime (q : ℝ) (p : ℝ) ≤ (p : ℝ))
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge)) (hΓ : HasEnhancingPaths enhanced Γ)
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge) (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp1.le)
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1.le))
        h Γ).map configToBool).toMeasure (G.fkPMF hq hp1.le ξ).toMeasure := by
  exact lower_comparison_of_auxiliary_paths G hq hp0 hp1 ξ enhanced
    (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1.le))
    (FK.prime_pos (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1.le))
    (FK.Finite.WiredEnhancement.prime_lt_one_interior
      (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)) h
    le_rfl Γ hΓ hpath ρ hρ auxiliary haux schedule hschedule

/-- **Proposition 3.2(2), actual finite labelled-multigraph FK model.** For
`q > 1`, the strict relation `FK.prime q p < p` is proved, and the exact
path-enhanced inhomogeneous product is stochastically below the FK law. -/
theorem lower_path_comparison_of_one_lt_q
    (G : LabelledMultigraph) {q p : NNReal} (hq1 : 1 < q)
    (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge)) (hΓ : HasEnhancingPaths enhanced Γ)
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge) (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp1.le)
        (FK.prime_mem_Icc (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
          (by exact_mod_cast hp0.le) (by exact_mod_cast hp1.le))
        (FK.Finite.WiredEnhancement.prime_lt_of_one_lt_q
          (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
          (by exact_mod_cast hp0) (by exact_mod_cast hp1)
          (by exact_mod_cast hq1)).le Γ).map configToBool).toMeasure
        (G.fkPMF (lt_trans zero_lt_one hq1) hp1.le ξ).toMeasure := by
  have hq : 0 < q := lt_trans zero_lt_one hq1
  have hlt : FK.prime (q : ℝ) (p : ℝ) < (p : ℝ) :=
    FK.Finite.WiredEnhancement.prime_lt_of_one_lt_q
      (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq1)
  exact prime_lower_comparison_of_auxiliary_paths G hq hp0 hp1 hlt.le ξ enhanced Γ hΓ
    hpath ρ hρ auxiliary haux schedule hschedule

end OpenPath.LowerPathCoupling
