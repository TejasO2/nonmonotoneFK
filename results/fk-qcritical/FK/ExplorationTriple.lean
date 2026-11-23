import FK.ExplorationSequential

/-!
# Sequential ordered triples with exact pair projections

Two ordered pair processes with a common upper coordinate can be revealed
simultaneously.  At each bit their one-step couplings are glued through the
common upper bit.  The two lower/upper history projections are exactly the
original pair processes.  This is the sequential form needed to condition
both FK coordinates on one and the same exploration stratum.
-/

namespace FK.Exploration.TripleSequential

open scoped ENNReal BigOperators
open FK.Exploration.Sequential

/-- Reveal `n` further ordered triples.  The history type is right nested:
`(first lower, second lower, upper)`. -/
noncomputable def extendTriple
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (x₁ x₂ y : List Bool) : ℕ → PMF (List Bool × List Bool × List Bool)
  | 0 => PMF.pure (x₁, x₂, y)
  | n + 1 => (step x₁ x₂ y).bind fun z =>
      extendTriple step (x₁ ++ [z.1]) (x₂ ++ [z.2.1]) (y ++ [z.2.2]) n

/-- Chronological concatenation of the triple process. -/
theorem extendTriple_add
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (x₁ x₂ y : List Bool) (m n : ℕ) :
    extendTriple step x₁ x₂ y (m + n) =
      (extendTriple step x₁ x₂ y m).bind fun z =>
        extendTriple step z.1 z.2.1 z.2.2 n := by
  induction m generalizing x₁ x₂ y with
  | zero => simp [extendTriple]
  | succ m ih =>
      simp only [Nat.succ_add, extendTriple]
      rw [PMF.bind_bind]
      congr 1
      funext z
      rw [ih]

/-- The first-lower/upper projection is the prescribed pair process. -/
theorem extendTriple_map_fst_thd
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (pair₁ : List Bool → List Bool → PMF (Bool × Bool))
    (hstep : ∀ x₁ x₂ y, (step x₁ x₂ y).map (fun z => (z.1, z.2.2)) = pair₁ x₁ y)
    (x₁ x₂ y : List Bool) (n : ℕ) :
    (extendTriple step x₁ x₂ y n).map (fun z => (z.1, z.2.2)) =
      extendPair pair₁ x₁ y n := by
  induction n generalizing x₁ x₂ y with
  | zero => simpa [extendTriple, extendPair] using
      PMF.pure_map (fun z : List Bool × List Bool × List Bool => (z.1, z.2.2)) (x₁, x₂, y)
  | succ n ih =>
      calc
        (extendTriple step x₁ x₂ y (n + 1)).map (fun z => (z.1, z.2.2)) =
            (step x₁ x₂ y).bind (fun z =>
              (extendTriple step (x₁ ++ [z.1]) (x₂ ++ [z.2.1]) (y ++ [z.2.2]) n).map
                (fun w => (w.1, w.2.2))) := PMF.map_bind _ _ _
        _ = (step x₁ x₂ y).bind (fun z =>
            extendPair pair₁ (x₁ ++ [z.1]) (y ++ [z.2.2]) n) := by
          congr 1
          funext z
          rw [ih]
        _ = ((step x₁ x₂ y).map (fun z => (z.1, z.2.2))).bind
            (fun w => extendPair pair₁ (x₁ ++ [w.1]) (y ++ [w.2]) n) := by
          rw [PMF.bind_map]
          rfl
        _ = (pair₁ x₁ y).bind (fun w =>
            extendPair pair₁ (x₁ ++ [w.1]) (y ++ [w.2]) n) := by
          rw [hstep]
        _ = extendPair pair₁ x₁ y (n + 1) := rfl

/-- The second-lower/upper projection is the prescribed pair process. -/
theorem extendTriple_map_snd_thd
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (pair₂ : List Bool → List Bool → PMF (Bool × Bool))
    (hstep : ∀ x₁ x₂ y, (step x₁ x₂ y).map (fun z => (z.2.1, z.2.2)) = pair₂ x₂ y)
    (x₁ x₂ y : List Bool) (n : ℕ) :
    (extendTriple step x₁ x₂ y n).map (fun z => (z.2.1, z.2.2)) =
      extendPair pair₂ x₂ y n := by
  induction n generalizing x₁ x₂ y with
  | zero => simpa [extendTriple, extendPair] using
      PMF.pure_map (fun z : List Bool × List Bool × List Bool => (z.2.1, z.2.2)) (x₁, x₂, y)
  | succ n ih =>
      calc
        (extendTriple step x₁ x₂ y (n + 1)).map (fun z => (z.2.1, z.2.2)) =
            (step x₁ x₂ y).bind (fun z =>
              (extendTriple step (x₁ ++ [z.1]) (x₂ ++ [z.2.1]) (y ++ [z.2.2]) n).map
                (fun w => (w.2.1, w.2.2))) := PMF.map_bind _ _ _
        _ = (step x₁ x₂ y).bind (fun z =>
            extendPair pair₂ (x₂ ++ [z.2.1]) (y ++ [z.2.2]) n) := by
          congr 1
          funext z
          rw [ih]
        _ = ((step x₁ x₂ y).map (fun z => (z.2.1, z.2.2))).bind
            (fun w => extendPair pair₂ (x₂ ++ [w.1]) (y ++ [w.2]) n) := by
          rw [PMF.bind_map]
          rfl
        _ = (pair₂ x₂ y).bind (fun w =>
            extendPair pair₂ (x₂ ++ [w.1]) (y ++ [w.2]) n) := by
          rw [hstep]
        _ = extendPair pair₂ x₂ y (n + 1) := rfl

/-- Both order relations to the common upper history persist on support. -/
theorem extendTriple_ordered
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (hstep : ∀ x₁ x₂ y z, z ∈ (step x₁ x₂ y).support →
      z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2)
    {x₁ x₂ y : List Bool}
    (h₁ : List.Forall₂ (fun a b : Bool => a ≤ b) x₁ y)
    (h₂ : List.Forall₂ (fun a b : Bool => a ≤ b) x₂ y)
    (n : ℕ) {z : List Bool × List Bool × List Bool}
    (hz : z ∈ (extendTriple step x₁ x₂ y n).support) :
    List.Forall₂ (fun a b : Bool => a ≤ b) z.1 z.2.2 ∧
      List.Forall₂ (fun a b : Bool => a ≤ b) z.2.1 z.2.2 := by
  induction n generalizing x₁ x₂ y z with
  | zero =>
      have h : z = (x₁, x₂, y) := (PMF.mem_support_pure_iff _ _).mp hz
      subst z
      exact ⟨h₁, h₂⟩
  | succ n ih =>
      rw [extendTriple, PMF.mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨hw₁, hw₂⟩ := hstep x₁ x₂ y w hw
      exact ih (forall₂_append_singleton h₁ hw₁) (forall₂_append_singleton h₂ hw₂) hz

/-- All three histories gain exactly `n` bits. -/
theorem extendTriple_length_support
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (x₁ x₂ y : List Bool) (n : ℕ) {z : List Bool × List Bool × List Bool}
    (hz : z ∈ (extendTriple step x₁ x₂ y n).support) :
    z.1.length = x₁.length + n ∧ z.2.1.length = x₂.length + n ∧
      z.2.2.length = y.length + n := by
  induction n generalizing x₁ x₂ y z with
  | zero =>
      have h : z = (x₁, x₂, y) := (PMF.mem_support_pure_iff _ _).mp hz
      subst z
      exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      rw [extendTriple, PMF.mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨h₁, h₂, h₃⟩ := ih (x₁ ++ [w.1]) (x₂ ++ [w.2.1]) (y ++ [w.2.2]) hz
      exact ⟨by simp only [List.length_append, List.length_singleton] at h₁ ⊢; omega,
        by simp only [List.length_append, List.length_singleton] at h₂ ⊢; omega,
        by simp only [List.length_append, List.length_singleton] at h₃ ⊢; omega⟩

end FK.Exploration.TripleSequential
