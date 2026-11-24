import Mathlib

/-!
# Reduced words over a two-class alphabet
-/

namespace Ultra

/-- The alphabet: three base letters and two activation letters. -/
abbrev A : Type := Sum (Fin 3) (Fin 2)

/-- Class of a letter: `0` for base letters, `1` for activation letters. -/
def acls : A → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- Reduced words: no two equal adjacent letters. -/
def Reduced : List A → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => a ≠ b ∧ Reduced (b :: l)

@[simp] lemma reduced_nil : Reduced ([] : List A) := trivial

@[simp] lemma reduced_singleton (a : A) : Reduced [a] := trivial

lemma Reduced.tail {a : A} {l : List A} (h : Reduced (a :: l)) : Reduced l := by
  cases l with
  | nil => exact reduced_nil
  | cons b t => exact h.2

lemma Reduced.cons_cons {a b : A} {l : List A} :
    Reduced (a :: b :: l) ↔ a ≠ b ∧ Reduced (b :: l) := Iff.rfl

lemma Reduced.cons_iff {a : A} {l : List A} :
    Reduced (a :: l) ↔ l = [] ∨ (a ≠ l.headD a ∧ Reduced l) := by
  cases l with
  | nil => simp [Reduced]
  | cons b t => simp [Reduced, eq_comm]

lemma Reduced.head?_ne {a : A} {l : List A} (h : Reduced (a :: l)) (hl : l ≠ []) :
    a ≠ l.headD a := by
  rcases (Reduced.cons_iff (a := a) (l := l)).1 h with h' | ⟨h', _⟩
  · exact absurd h' hl
  · exact h'

lemma getLast?_cons_cons (b c : A) (t : List A) :
    (b :: c :: t).getLast? = (c :: t).getLast? := by
  cases t with
  | nil => rfl
  | cons d t => simp [List.getLast?_cons]

lemma Reduced.snoc_iff (l : List A) (a : A) :
    Reduced (l ++ [a]) ↔ Reduced l ∧ (l = [] ∨ l.getLast? ≠ some a) := by
  induction l with
  | nil => simp [Reduced]
  | cons b t ih =>
    cases t with
    | nil => simp [Reduced]
    | cons c t =>
      have h1 : Reduced (b :: (c :: t) ++ [a]) ↔ b ≠ c ∧ Reduced ((c :: t) ++ [a]) :=
        Reduced.cons_cons
      rw [h1, ih, getLast?_cons_cons, Reduced.cons_cons]
      simp only [List.cons_ne_nil, false_or, ne_eq, Option.some.injEq]
      tauto

lemma Reduced.of_snoc {l : List A} {a : A} (h : Reduced (l ++ [a])) : Reduced l :=
  ((Reduced.snoc_iff l a).1 h).1

lemma Reduced.snoc_of_ne {l : List A} {a : A} (h : Reduced l)
    (hl : l = [] ∨ l.getLast? ≠ some a) : Reduced (l ++ [a]) :=
  (Reduced.snoc_iff l a).2 ⟨h, hl⟩

lemma Reduced.getLast?_ne {l : List A} {a : A} (h : Reduced (l ++ [a])) (hl : l ≠ []) :
    l.getLast? ≠ some a := by
  rcases ((Reduced.snoc_iff l a).1 h).2 with h' | h'
  · exact absurd h' hl
  · exact h'

end Ultra
