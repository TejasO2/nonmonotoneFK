import FK.EssentialEnhancement
import CurvatureVariance.Infra.Percolation.Balls

/-!
# The peeling step in the essential-enhancement argument

For an increasing event, a coordinate is pivotal if forcing it open puts the
configuration in the event and forcing it closed puts it outside. The main
result below formalizes the first step of the Aizenman--Grimmett local
pivot-comparison argument. Starting with an event at `ω` and a pivotal
coordinate `e`, remove a list of candidate enhancement coordinates one at a
time. Either the first removal which destroys the event supplies a second
pivotal coordinate, or the entire list can be removed while retaining the
event. In both cases the original coordinate remains pivotal. The new
configuration differs from `ω` only on (a prefix of) the given list.

We then specialize this statement to configurations with separate bond and
activation coordinates, and to pullbacks of the finite one-arm events used in
Bernoulli percolation. This is a deterministic finite-volume ingredient; it
is not the strict critical-point theorem itself.
-/

open Set
open FK.EssentialEnhancement
open CurvatureVariance.Infra.Percolation

namespace FK.AGPeeling

universe u v w

/-- `e` is pivotal for `A` at `ω` when opening `e` gives the event and closing
`e` does not. The actual value of `ω e` is irrelevant. -/
def Pivotal {E : Type u} (A : Set (E → Bool)) (e : E) (ω : E → Bool) : Prop :=
  forceEdge ω e true ∈ A ∧ forceEdge ω e false ∉ A

/-- Close every coordinate in a list, from left to right. -/
noncomputable def closeList {E : Type u} (ω : E → Bool) : List E → (E → Bool)
  | [] => ω
  | e :: l => closeList (forceEdge ω e false) l

/-- Two configurations agree away from the coordinates in `l`. -/
def AgreesOutside {E : Type u} (l : List E) (ω η : E → Bool) : Prop :=
  ∀ e, e ∉ l → ω e = η e

lemma le_forceEdge_true {E : Type u} (ω : E → Bool) (e : E) :
    ω ≤ forceEdge ω e true := by
  intro f
  by_cases h : f = e
  · subst f
    simp
  · rw [forceEdge_of_ne _ h]

lemma forceEdge_false_le {E : Type u} (ω : E → Bool) (e : E) :
    forceEdge ω e false ≤ ω := by
  intro f
  by_cases h : f = e
  · subst f
    simp
  · rw [forceEdge_of_ne _ h]

lemma forceEdge_mono {E : Type u} {ω η : E → Bool} (hωη : ω ≤ η)
    (e : E) (b : Bool) : forceEdge ω e b ≤ forceEdge η e b := by
  intro f
  by_cases h : f = e
  · subst f
    simp
  · simpa only [forceEdge_of_ne _ h] using hωη f

lemma closeList_le {E : Type u} (ω : E → Bool) (l : List E) :
    closeList ω l ≤ ω := by
  induction l generalizing ω with
  | nil => exact le_rfl
  | cons e l ih =>
      exact (ih (forceEdge ω e false)).trans (forceEdge_false_le ω e)

lemma closeList_agreesOutside {E : Type u} (ω : E → Bool) (l : List E) :
    AgreesOutside l ω (closeList ω l) := by
  induction l generalizing ω with
  | nil => intro e he; rfl
  | cons z l ih =>
      intro f hf
      have hfz : f ≠ z := by
        intro h
        exact hf (by simp [h])
      have hfl : f ∉ l := by
        intro h
        exact hf (by simp [h])
      calc
        ω f = forceEdge ω z false f := (forceEdge_of_ne _ hfz false).symm
        _ = closeList (forceEdge ω z false) l f := ih (forceEdge ω z false) f hfl

/-- Pivotal coordinates survive a decrease of the other coordinates as long as
the decreased configuration still belongs to the increasing event. -/
lemma Pivotal.of_mem_of_le {E : Type u} {A : Set (E → Bool)}
    (hA : IsUpperSet A) {ω η : E → Bool} (hη : η ∈ A) (hηω : η ≤ ω)
    {e : E} (he : Pivotal A e ω) : Pivotal A e η := by
  constructor
  · exact hA (le_forceEdge_true η e) hη
  · intro hclosed
    exact he.2 (hA (forceEdge_mono hηω e false) hclosed)

/-- **The pivot-peeling dichotomy.** Remove candidate coordinates from left to
right. If the event survives every removal, the final configuration is a
witness to the second branch. Otherwise, the configuration immediately before
the first failed removal witnesses the first branch, and the removed coordinate
is pivotal there. -/
theorem peel {E : Type u} {A : Set (E → Bool)} (hA : IsUpperSet A)
    {ω : E → Bool} (hω : ω ∈ A) (l : List E) :
    (∃ z ∈ l, ∃ η, η ∈ A ∧ η ≤ ω ∧ AgreesOutside l ω η ∧ Pivotal A z η) ∨
      closeList ω l ∈ A := by
  induction l generalizing ω with
  | nil => exact Or.inr hω
  | cons z l ih =>
      by_cases hz : forceEdge ω z false ∈ A
      · rcases ih hz with h | h
        · obtain ⟨x, hx, η, hη, hηle, hout, hpiv⟩ := h
          left
          refine ⟨x, List.mem_cons_of_mem z hx, η, hη,
            hηle.trans (forceEdge_false_le ω z), ?_, hpiv⟩
          intro f hf
          have hfz : f ≠ z := by
            intro h
            exact hf (by simp [h])
          have hfl : f ∉ l := by
            intro h
            exact hf (by simp [h])
          calc
            ω f = forceEdge ω z false f := (forceEdge_of_ne _ hfz false).symm
            _ = η f := hout f hfl
        · exact Or.inr h
      · left
        refine ⟨z, by simp, ω, hω, le_rfl, ?_, ?_⟩
        · intro f hf; rfl
        · exact ⟨hA (le_forceEdge_true ω z) hω, hz⟩

/-- Peeling preserves a prescribed pivotal coordinate in either branch. -/
theorem peel_preserving_pivotal {E : Type u} {A : Set (E → Bool)}
    (hA : IsUpperSet A) {ω : E → Bool} (hω : ω ∈ A) (l : List E)
    {e : E} (he : Pivotal A e ω) :
    (∃ z ∈ l, ∃ η, η ∈ A ∧ η ≤ ω ∧ AgreesOutside l ω η ∧
        Pivotal A z η ∧ Pivotal A e η) ∨
      (closeList ω l ∈ A ∧ Pivotal A e (closeList ω l)) := by
  rcases peel hA hω l with h | h
  · obtain ⟨z, hz, η, hη, hle, hout, hpiv⟩ := h
    exact Or.inl ⟨z, hz, η, hη, hle, hout, hpiv,
      Pivotal.of_mem_of_le hA hη hle he⟩
  · exact Or.inr ⟨h, Pivotal.of_mem_of_le hA h (closeList_le ω l) he⟩

/-- A joint configuration has independent bond and enhancement-activation
coordinates. -/
abbrev JointConfig (E : Type u) (F : Type v) := E ⊕ F → Bool

/-- Pivotality of a bond in a joint bond/activation configuration. -/
def EdgePivotal {E : Type u} {F : Type v} (A : Set (JointConfig E F))
    (e : E) (ω : JointConfig E F) : Prop :=
  Pivotal A (Sum.inl e) ω

/-- Pivotality of an enhancement activation in a joint configuration. -/
def ActivationPivotal {E : Type u} {F : Type v} (A : Set (JointConfig E F))
    (z : F) (ω : JointConfig E F) : Prop :=
  Pivotal A (Sum.inr z) ω

/-- Close exactly the activations in `l`, leaving every bond untouched. -/
noncomputable def closeActivations {E : Type u} {F : Type v} (l : List F)
    (ω : JointConfig E F) : JointConfig E F :=
  closeList ω (l.map Sum.inr)

/-- The joint form of `peel_preserving_pivotal`: either some activation in the
candidate list becomes pivotal after changing only earlier activations in that
list, or all candidate activations can be closed without losing the original
bond pivot. -/
theorem peel_activations {E : Type u} {F : Type v} {A : Set (JointConfig E F)}
    (hA : IsUpperSet A) {ω : JointConfig E F} (hω : ω ∈ A) (l : List F)
    {e : E} (he : EdgePivotal A e ω) :
    (∃ z ∈ l, ∃ η, η ∈ A ∧ η ≤ ω ∧
        AgreesOutside (l.map Sum.inr) ω η ∧
        ActivationPivotal A z η ∧ EdgePivotal A e η) ∨
      (closeActivations l ω ∈ A ∧ EdgePivotal A e (closeActivations l ω)) := by
  rcases peel_preserving_pivotal hA hω (l.map Sum.inr) he with h | h
  · obtain ⟨x, hx, η, hη, hle, hout, hxpiv, hepiv⟩ := h
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Or.inl ⟨z, hz, η, hη, hle, hout, hxpiv, hepiv⟩
  · exact Or.inr h

/-- Pull back a bond event by forgetting all enhancement activations. -/
def bondEvent {E : Type u} {F : Type v} (B : Set (E → Bool)) :
    Set (JointConfig E F) :=
  (fun ω e => ω (Sum.inl e)) ⁻¹' B

lemma isUpperSet_bondEvent {E : Type u} {F : Type v} {B : Set (E → Bool)}
    (hB : IsUpperSet B) : IsUpperSet (bondEvent (F := F) B) := by
  intro ω η hωη hω
  exact hB (fun e => hωη (Sum.inl e)) hω

/-- The finite one-arm event on the bond coordinates of a joint configuration. -/
def jointArmEvent {V : Type w} (G : SimpleGraph V) (F : Type v)
    (o : V) (n : ℕ) : Set (JointConfig G.edgeSet F) :=
  bondEvent (armEvent G o n)

lemma isUpperSet_jointArmEvent {V : Type w} (G : SimpleGraph V) (F : Type v)
    (o : V) (n : ℕ) : IsUpperSet (jointArmEvent G F o n) :=
  isUpperSet_bondEvent (isUpperSet_armEvent o n)

/-- The peeling theorem for an actual finite-volume one-arm event. -/
theorem peel_jointArmEvent {V : Type w} (G : SimpleGraph V) {F : Type v}
    (o : V) (n : ℕ) {ω : JointConfig G.edgeSet F}
    (hω : ω ∈ jointArmEvent G F o n) (l : List F)
    {e : G.edgeSet} (he : EdgePivotal (jointArmEvent G F o n) e ω) :
    (∃ z ∈ l, ∃ η, η ∈ jointArmEvent G F o n ∧ η ≤ ω ∧
        AgreesOutside (l.map Sum.inr) ω η ∧
        ActivationPivotal (jointArmEvent G F o n) z η ∧
        EdgePivotal (jointArmEvent G F o n) e η) ∨
      (closeActivations l ω ∈ jointArmEvent G F o n ∧
        EdgePivotal (jointArmEvent G F o n) e (closeActivations l ω)) :=
  peel_activations (isUpperSet_jointArmEvent G F o n) hω l he

end FK.AGPeeling
