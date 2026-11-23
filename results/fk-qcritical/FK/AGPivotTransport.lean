import FK.AGPeeling
import FK.OpenPathEnhancement

/-!
# Finite probability transport for bounded-local pivot maps

A deterministic modification of a finite configuration does not preserve
product mass exactly.  If it changes only a fixed finite set of coordinates,
however, positive lower bounds on the coordinate masses give a uniform
one-sided likelihood-ratio bound.  Together with a bound on the source fibres,
this transports event probabilities without assuming that the modification is
injective.

This is the finite change-of-variables component of the Aizenman--Grimmett
pivot argument.  It does not construct the enhancement gadget and does not
assert a strict inequality between critical points.
-/

open Set
open scoped BigOperators

namespace FK.AGPeeling

open OpenPath

universe u v

/-- A deterministic map with at most `k` source configurations in each fibre
transports an event bound whenever its point masses satisfy the displayed
one-sided comparison.  The source fibres are counted only inside `S`. -/
theorem event_mul_le_of_bounded_fibres {Ω : Type u} [Fintype Ω]
    (μ : FinProb Ω) (S B : Set Ω) (T : Ω → Ω) (c : ℝ) (k : ℕ)
    (hmap : ∀ ω ∈ S, T ω ∈ B)
    (hmass : ∀ ω ∈ S, c * μ.mass ω ≤ μ.mass (T ω))
    (hfibre : ∀ η ∈ B, {ω | ω ∈ S ∧ T ω = η}.ncard ≤ k) :
    c * μ.event S ≤ (k : ℝ) * μ.event B := by
  classical
  let s : Finset Ω := Finset.univ.filter fun ω => ω ∈ S
  let t : Finset Ω := Finset.univ.filter fun η => η ∈ B
  have hs {ω : Ω} (hω : ω ∈ s) : ω ∈ S := by
    simpa [s] using (Finset.mem_filter.mp hω).2
  have ht {η : Ω} (hη : η ∈ t) : η ∈ B := by
    simpa [t] using (Finset.mem_filter.mp hη).2
  have hmaps : ∀ ω ∈ s, T ω ∈ t := by
    intro ω hω
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmap ω (hs hω)
  have hfibre' (η : Ω) (hη : η ∈ t) :
      (s.filter fun ω => T ω = η).card ≤ k := by
    have heq : (↑(s.filter fun ω => T ω = η) : Set Ω) =
        {ω | ω ∈ S ∧ T ω = η} := by
      ext ω
      simp [s]
    rw [← Set.ncard_coe_finset, heq]
    exact hfibre η (ht hη)
  calc
    c * μ.event S = ∑ ω ∈ s, c * μ.mass ω := by
      simp [s, FinProb.event, Finset.sum_filter, Finset.mul_sum]
    _ ≤ ∑ ω ∈ s, μ.mass (T ω) := by
      exact Finset.sum_le_sum fun ω hω => hmass ω (hs hω)
    _ = ∑ η ∈ t, ∑ _ω ∈ s.filter (fun ω => T ω = η), μ.mass η := by
      simpa using (Finset.sum_fiberwise_of_maps_to' hmaps μ.mass).symm
    _ = ∑ η ∈ t, (s.filter (fun ω => T ω = η)).card • μ.mass η := by
      simp only [Finset.sum_const]
    _ ≤ ∑ η ∈ t, k • μ.mass η := by
      apply Finset.sum_le_sum
      intro η hη
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hfibre' η hη))
        (μ.mass_nonneg η)
    _ = (k : ℝ) * μ.event B := by
      simp [t, FinProb.event, Finset.sum_filter, Finset.mul_sum]

end FK.AGPeeling

namespace FK.AGPeeling

open OpenPath

/-- A point mass of a finite probability law is at most one. -/
lemma FinProb_mass_le_one {Ω : Type u} [Fintype Ω] (μ : FinProb Ω) (ω : Ω) :
    μ.mass ω ≤ 1 := by
  calc
    μ.mass ω ≤ ∑ η, μ.mass η := by
      exact Finset.single_le_sum (fun η _ => μ.mass_nonneg η) (Finset.mem_univ ω)
    _ = 1 := μ.sum_mass

/-- A local map leaves the configuration unchanged away from `R`. -/
def IsLocalModification {E : Type u} (R : Finset E)
    (T : (E → Bool) → (E → Bool)) : Prop :=
  ∀ ω e, e ∉ R → T ω e = ω e

/-- A source fibre of an `R`-local Boolean modification has at most `2 ^ |R|`
configurations.  The restriction to `R` is a complete invariant of the fibre. -/
lemma ncard_local_fibre_le {E : Type u} [DecidableEq E]
    (R : Finset E) (T : (E → Bool) → (E → Bool))
    (hT : IsLocalModification R T) (S : Set (E → Bool)) (η : E → Bool) :
    {ω | ω ∈ S ∧ T ω = η}.ncard ≤ 2 ^ R.card := by
  classical
  let f : (E → Bool) → (↥R → Bool) := fun ω e => ω e
  have hf : Set.InjOn f {ω | ω ∈ S ∧ T ω = η} := by
    intro ω hω ξ hξ hωξ
    funext e
    by_cases he : e ∈ R
    · exact congrFun hωξ ⟨e, he⟩
    · calc
        ω e = T ω e := (hT ω e he).symm
        _ = η e := congrFun hω.2 e
        _ = T ξ e := (congrFun hξ.2 e).symm
        _ = ξ e := hT ξ e he
  have hcard := Set.ncard_le_ncard_of_injOn f
    (fun ω _ => Set.mem_univ (f ω)) hf Set.finite_univ
  simpa [Set.ncard_eq_toFinset_card, Nat.card_eq_fintype_card,
    Fintype.card_fun] using hcard

/-- For independent finite Boolean coordinates, an `R`-local modification
multiplies every source point mass by at most `δ ^ |R|` in the one-sided
comparison to its image.  Here `δ` is a common lower bound for both values of
every coordinate; consequently `0 < δ` also makes every configuration mass
positive. -/
lemma pi_mass_pow_mul_le_of_local {E : Type u} [Fintype E] [DecidableEq E]
    (ν : E → FinProb Bool) (R : Finset E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδν : ∀ e b, δ ≤ (ν e).mass b) (ω η : E → Bool)
    (hout : ∀ e, e ∉ R → ω e = η e) :
    δ ^ R.card * (FinProb.pi ν).mass ω ≤ (FinProb.pi ν).mass η := by
  have hR : δ ^ R.card * (∏ e ∈ R, (ν e).mass (ω e)) ≤
      ∏ e ∈ R, (ν e).mass (η e) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro e he
      exact mul_nonneg hδ ((ν e).mass_nonneg (ω e))
    · intro e he
      calc
        δ * (ν e).mass (ω e) ≤ δ * 1 :=
          mul_le_mul_of_nonneg_left (FinProb_mass_le_one (ν e) (ω e)) hδ
        _ = δ := mul_one δ
        _ ≤ (ν e).mass (η e) := hδν e (η e)
  have houtprod : (∏ e ∈ Rᶜ, (ν e).mass (ω e)) =
      ∏ e ∈ Rᶜ, (ν e).mass (η e) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [hout e (by simpa using he)]
  simp only [FinProb.pi_mass, ← Finset.prod_mul_prod_compl R]
  rw [houtprod]
  calc
    δ ^ R.card * ((∏ e ∈ R, (ν e).mass (ω e)) *
        ∏ e ∈ Rᶜ, (ν e).mass (η e)) =
        (δ ^ R.card * ∏ e ∈ R, (ν e).mass (ω e)) *
          ∏ e ∈ Rᶜ, (ν e).mass (η e) := by ring
    _ ≤ (∏ e ∈ R, (ν e).mass (η e)) * ∏ e ∈ Rᶜ, (ν e).mass (η e) :=
      mul_le_mul_of_nonneg_right hR
        (Finset.prod_nonneg fun e _ => (ν e).mass_nonneg (η e))

/-- **Bounded-local product-probability transport.**  An `R`-local modification
needs no separately hypothesized fibre bound or likelihood-ratio estimate:
both follow from its support and from independent finite Boolean coordinate
laws.  The target event `B` need not be the whole image of `S`. -/
theorem local_pi_event_mul_le {E : Type u} [Fintype E] [DecidableEq E]
    (ν : E → FinProb Bool) (R : Finset E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδν : ∀ e b, δ ≤ (ν e).mass b)
    (T : (E → Bool) → (E → Bool)) (hT : IsLocalModification R T)
    (S B : Set (E → Bool)) (hmap : ∀ ω ∈ S, T ω ∈ B) :
    δ ^ R.card * (FinProb.pi ν).event S ≤
      ((2 ^ R.card : ℕ) : ℝ) * (FinProb.pi ν).event B := by
  apply event_mul_le_of_bounded_fibres (FinProb.pi ν) S B T
    (δ ^ R.card) (2 ^ R.card) hmap
  · intro ω hω
    exact pi_mass_pow_mul_le_of_local ν R δ hδ hδν ω (T ω)
      (fun e he => (hT ω e he).symm)
  · intro η hη
    exact ncard_local_fibre_le R T hT S η

/-- Closing a list changes no coordinate outside that list. -/
theorem closeList_isLocalModification {E : Type u} [DecidableEq E]
    (l : List E) : IsLocalModification l.toFinset (closeList · l) := by
  intro ω e he
  exact (closeList_agreesOutside ω l e (by simpa using he)).symm

/-- Closing activation coordinates is supported on the listed activations;
all bond coordinates and all other activations are unchanged. -/
theorem closeActivations_isLocalModification {E : Type u} {F : Type v}
    [DecidableEq E] [DecidableEq F] (l : List F) :
    IsLocalModification (l.map (Sum.inr : F → E ⊕ F)).toFinset
      (closeActivations (E := E) l) := by
  intro ω x hx
  exact (closeList_agreesOutside (E := E ⊕ F) ω (l.map Sum.inr) x
    (by simpa using hx)).symm

end FK.AGPeeling

namespace FK.AGPeeling

open OpenPath

/-- The pivot-branch form of `local_pi_event_mul_le`.  Bond and activation
coordinates have their own (possibly different and inhomogeneous) finite Bool
laws, and the product uses `Sum.elim` without identifying the two classes.

The only pivot-specific input left is `hmap`: the proposed local modification
must really send configurations where `e` is bond-pivotal to configurations
with an activation pivot on the candidate list `l`.  This is the geometric
peeling/gadget obligation; it is not assumed away by the probability lemma. -/
theorem local_joint_edgePivotal_event_mul_le
    {E : Type u} {F : Type v} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (bond : E → FinProb Bool) (activation : F → FinProb Bool)
    (R : Finset (E ⊕ F)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (T : JointConfig E F → JointConfig E F) (hT : IsLocalModification R T)
    (A : Set (JointConfig E F)) (e : E) (l : List F)
    (hmap : ∀ ω, EdgePivotal A e ω →
      ∃ z ∈ l, ActivationPivotal A z (T ω)) :
    δ ^ R.card * (FinProb.pi (Sum.elim bond activation)).event
        {ω | EdgePivotal A e ω} ≤
      ((2 ^ R.card : ℕ) : ℝ) * (FinProb.pi (Sum.elim bond activation)).event
        {η | ∃ z ∈ l, ActivationPivotal A z η} := by
  apply local_pi_event_mul_le (Sum.elim bond activation) R δ hδ
  · intro x b
    cases x with
    | inl e => exact hbond e b
    | inr z => exact hactivation z b
  · exact hT
  · intro ω hω
    exact hmap ω hω

end FK.AGPeeling

namespace FK.AGPeeling

open OpenPath

/-- The target data supplied by the activation-pivot branch of
`peel_activations`, with the new configuration placed first so that it can be
chosen canonically. -/
def HasActivationPeelWitness {E : Type u} {F : Type v}
    (A : Set (JointConfig E F)) (e : E) (l : List F)
    (ω : JointConfig E F) : Prop :=
  ∃ η, η ∈ A ∧ η ≤ ω ∧ AgreesOutside (l.map Sum.inr) ω η ∧
    EdgePivotal A e η ∧ ∃ z ∈ l, ActivationPivotal A z η

/-- Choose the activation-peeling target when it exists, and otherwise leave
`ω` unchanged.  Only the first case is used in the probability transport. -/
noncomputable def activationPeelTarget {E : Type u} {F : Type v}
    (A : Set (JointConfig E F)) (e : E) (l : List F)
    (ω : JointConfig E F) : JointConfig E F := by
  classical
  exact if h : HasActivationPeelWitness A e l ω then Classical.choose h else ω

lemma activationPeelTarget_spec {E : Type u} {F : Type v}
    (A : Set (JointConfig E F)) (e : E) (l : List F)
    (ω : JointConfig E F) (h : HasActivationPeelWitness A e l ω) :
    activationPeelTarget A e l ω ∈ A ∧
      activationPeelTarget A e l ω ≤ ω ∧
      AgreesOutside (l.map Sum.inr) ω (activationPeelTarget A e l ω) ∧
      EdgePivotal A e (activationPeelTarget A e l ω) ∧
      ∃ z ∈ l, ActivationPivotal A z (activationPeelTarget A e l ω) := by
  simp only [activationPeelTarget, h, ↓reduceDIte]
  exact Classical.choose_spec h

/-- The canonical target is supported on the same listed activations as the
peeling map.  Away from the witness branch it is the identity. -/
theorem activationPeelTarget_isLocalModification {E : Type u} {F : Type v}
    [DecidableEq E] [DecidableEq F]
    (A : Set (JointConfig E F)) (e : E) (l : List F) :
    IsLocalModification (l.map (Sum.inr : F → E ⊕ F)).toFinset
      (activationPeelTarget A e l) := by
  intro ω x hx
  by_cases h : HasActivationPeelWitness A e l ω
  · exact ((activationPeelTarget_spec A e l ω h).2.2.1 x
      (by simpa using hx)).symm
  · simp [activationPeelTarget, h]

/-- Probability of the actual activation-pivot branch of `peel_activations`.
The local target and its pivot property are obtained from the peeling witness,
so no modification-map or map-validity hypothesis remains here. -/
theorem activationPeel_branch_event_mul_le
    {E : Type u} {F : Type v} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (bond : E → FinProb Bool) (activation : F → FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (A : Set (JointConfig E F)) (e : E) (l : List F) :
    let R := (l.map (Sum.inr : F → E ⊕ F)).toFinset
    let μ := FinProb.pi (Sum.elim bond activation)
    δ ^ R.card * μ.event
        {ω | ω ∈ A ∧ EdgePivotal A e ω ∧ HasActivationPeelWitness A e l ω} ≤
      ((2 ^ R.card : ℕ) : ℝ) * μ.event
        {η | η ∈ A ∧ EdgePivotal A e η ∧
          ∃ z ∈ l, ActivationPivotal A z η} := by
  dsimp only
  apply local_pi_event_mul_le (Sum.elim bond activation)
    (l.map (Sum.inr : F → E ⊕ F)).toFinset δ hδ
  · intro x b
    cases x with
    | inl e => exact hbond e b
    | inr z => exact hactivation z b
  · exact activationPeelTarget_isLocalModification A e l
  · intro ω hω
    obtain ⟨hmem, hle, hout, hepiv, z, hz, hzpiv⟩ :=
      activationPeelTarget_spec A e l ω hω.2.2
    exact ⟨hmem, hepiv, z, hz, hzpiv⟩

/-- Probability of the complementary close-all branch.  If there is no
activation-peeling witness, `peel_activations` itself proves that closing all
candidate activations retains the event and the original bond pivot. -/
theorem closeActivations_branch_event_mul_le
    {E : Type u} {F : Type v} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (bond : E → FinProb Bool) (activation : F → FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (A : Set (JointConfig E F)) (hA : IsUpperSet A) (e : E) (l : List F) :
    let R := (l.map (Sum.inr : F → E ⊕ F)).toFinset
    let μ := FinProb.pi (Sum.elim bond activation)
    δ ^ R.card * μ.event
        {ω | ω ∈ A ∧ EdgePivotal A e ω ∧ ¬ HasActivationPeelWitness A e l ω} ≤
      ((2 ^ R.card : ℕ) : ℝ) * μ.event {η | η ∈ A ∧ EdgePivotal A e η} := by
  dsimp only
  apply local_pi_event_mul_le (Sum.elim bond activation)
    (l.map (Sum.inr : F → E ⊕ F)).toFinset δ hδ
  · intro x b
    cases x with
    | inl e => exact hbond e b
    | inr z => exact hactivation z b
  · exact closeActivations_isLocalModification l
  · intro ω hω
    rcases peel_activations hA hω.1 l hω.2.1 with h | h
    · obtain ⟨z, hz, η, hη, hηle, hout, hzpiv, hepiv⟩ := h
      exact False.elim (hω.2.2 ⟨η, hη, hηle, hout, hepiv, z, hz, hzpiv⟩)
    · exact h

end FK.AGPeeling

namespace FK.AGPeeling

open OpenPath

/-- Split a finite probability event on an arbitrary predicate. -/
lemma FinProb_event_split {Ω : Type u} [Fintype Ω]
    (μ : FinProb Ω) (S : Set Ω) (P : Ω → Prop) :
    μ.event S = μ.event {ω | ω ∈ S ∧ P ω} + μ.event {ω | ω ∈ S ∧ ¬ P ω} := by
  classical
  unfold FinProb.event
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : P ω <;> simp [h]

/-- The full finite probability comparison furnished by activation peeling.
The two sources in the preceding lemmas partition the event that `e` is
bond-pivotal in a configuration of `A`.  The first target has a listed
activation pivot; the second retains the bond pivot after all candidate
activations have been closed.  Overlap between the targets is harmless because
the conclusion sums their probabilities. -/
theorem peel_activations_event_mul_le_sum
    {E : Type u} {F : Type v} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (bond : E → FinProb Bool) (activation : F → FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (A : Set (JointConfig E F)) (hA : IsUpperSet A) (e : E) (l : List F) :
    let R := (l.map (Sum.inr : F → E ⊕ F)).toFinset
    let μ := FinProb.pi (Sum.elim bond activation)
    δ ^ R.card * μ.event {ω | ω ∈ A ∧ EdgePivotal A e ω} ≤
      ((2 ^ R.card : ℕ) : ℝ) * μ.event
          {η | η ∈ A ∧ EdgePivotal A e η ∧
            ∃ z ∈ l, ActivationPivotal A z η} +
        ((2 ^ R.card : ℕ) : ℝ) * μ.event {η | η ∈ A ∧ EdgePivotal A e η} := by
  dsimp only
  have hfirst := activationPeel_branch_event_mul_le bond activation δ hδ
    hbond hactivation A e l
  have hsecond := closeActivations_branch_event_mul_le bond activation δ hδ
    hbond hactivation A hA e l
  dsimp only at hfirst hsecond
  calc
    δ ^ (l.map (Sum.inr : F → E ⊕ F)).toFinset.card *
        (FinProb.pi (Sum.elim bond activation)).event
          {ω | ω ∈ A ∧ EdgePivotal A e ω} =
        δ ^ (l.map (Sum.inr : F → E ⊕ F)).toFinset.card *
          ((FinProb.pi (Sum.elim bond activation)).event
            {ω | (ω ∈ A ∧ EdgePivotal A e ω) ∧ HasActivationPeelWitness A e l ω} +
           (FinProb.pi (Sum.elim bond activation)).event
            {ω | (ω ∈ A ∧ EdgePivotal A e ω) ∧ ¬ HasActivationPeelWitness A e l ω}) := by
      rw [FinProb_event_split (FinProb.pi (Sum.elim bond activation))
        {ω | ω ∈ A ∧ EdgePivotal A e ω} (HasActivationPeelWitness A e l)]
      simp only [Set.mem_ofPred_eq]
    _ = δ ^ (l.map (Sum.inr : F → E ⊕ F)).toFinset.card *
          (FinProb.pi (Sum.elim bond activation)).event
            {ω | (ω ∈ A ∧ EdgePivotal A e ω) ∧ HasActivationPeelWitness A e l ω} +
        δ ^ (l.map (Sum.inr : F → E ⊕ F)).toFinset.card *
          (FinProb.pi (Sum.elim bond activation)).event
            {ω | (ω ∈ A ∧ EdgePivotal A e ω) ∧ ¬ HasActivationPeelWitness A e l ω} := by
      rw [mul_add]
    _ ≤ ((2 ^ (l.map (Sum.inr : F → E ⊕ F)).toFinset.card : ℕ) : ℝ) *
          (FinProb.pi (Sum.elim bond activation)).event
            {η | η ∈ A ∧ EdgePivotal A e η ∧
              ∃ z ∈ l, ActivationPivotal A z η} +
        ((2 ^ (l.map (Sum.inr : F → E ⊕ F)).toFinset.card : ℕ) : ℝ) *
          (FinProb.pi (Sum.elim bond activation)).event
            {η | η ∈ A ∧ EdgePivotal A e η} := by
      exact add_le_add
        (by simpa only [and_assoc] using hfirst)
        (by simpa only [and_assoc] using hsecond)

end FK.AGPeeling
