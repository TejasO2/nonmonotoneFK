import Mathlib

/-!
# Preparation for the countable (Cantor-space) Strassen lift

This file isolates, sorry-free, the measure-theoretic identities that a measure-level
lift of `FiniteTransport.finite_strassen` from finite to countably infinite coordinate
sets needs.  The unconditional finite results live in `Transport.lean`; this file only
records that the disintegration API Mathlib provides is applicable to the concrete
profinite projection, so the remaining gap is exactly the fibre-support computation and
the marginal computation described in `README.md`.

Nothing here asserts the countable theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CountableStrassen

/-- Restriction of a configuration of `ℕ` bits to its first `n` coordinates. -/
def proj (n : ℕ) : (ℕ → Bool) → (Fin n → Bool) := fun x i => x i

lemma measurable_proj (n : ℕ) : Measurable (proj n) := by
  unfold proj; fun_prop

/-- The graph map `x ↦ (x|_n, x)`. -/
def graphMap (n : ℕ) : (ℕ → Bool) → (Fin n → Bool) × (ℕ → Bool) :=
  fun x => (proj n x, x)

lemma measurable_graphMap (n : ℕ) : Measurable (graphMap n) := by
  unfold graphMap
  exact (measurable_proj n).prod measurable_id

/-- The first marginal of the graph law is the `n`-th finite marginal. -/
theorem graphMap_fst (n : ℕ) (μ : Measure (ℕ → Bool)) :
    (μ.map (graphMap n)).fst = μ.map (proj n) := by
  have hid : Prod.fst ∘ graphMap n = proj n := by
    funext x; rfl
  rw [Measure.fst, Measure.map_map measurable_fst (measurable_graphMap n), hid]

/-- The second marginal of the graph law is the original measure. -/
theorem graphMap_snd (n : ℕ) (μ : Measure (ℕ → Bool)) :
    (μ.map (graphMap n)).snd = μ := by
  have hid : Prod.snd ∘ graphMap n = id := by
    funext x; rfl
  rw [Measure.snd, Measure.map_map measurable_snd (measurable_graphMap n), hid, Measure.map_id]

/-- **Disintegration identity.**  Every probability measure on the Cantor space is the
composition of its `n`-th finite marginal with the conditional kernel of its graph law. -/
theorem graphMap_disintegrate (n : ℕ) (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] :
    μ.map (graphMap n) = (μ.map (proj n)) ⊗ₘ (μ.map (graphMap n)).condKernel := by
  rw [← graphMap_fst n μ]
  exact (Measure.disintegrate (μ.map (graphMap n)) (μ.map (graphMap n)).condKernel).symm

/-- The order condition at finite level `n`, as a set of pairs of configurations. -/
def levelOrder (n : ℕ) : Set ((ℕ → Bool) × (ℕ → Bool)) :=
  {z | proj n z.1 ≤ proj n z.2}

/-- The full order condition is the countable intersection of the finite-level ones. -/
theorem order_eq_all_levelOrder :
    {z : (ℕ → Bool) × (ℕ → Bool) | z.1 ≤ z.2} = {z | ∀ n, z ∈ levelOrder n} := by
  ext z
  constructor
  · intro h n i
    exact h ↑i
  · intro h e
    exact h (e + 1) ⟨e, Nat.lt_succ_self e⟩

end CountableStrassen
