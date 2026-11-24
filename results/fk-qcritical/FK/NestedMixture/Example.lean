import FK.NestedMixture.Limit

/-!
# Non-vacuity of the growing-family hypotheses

A concrete growing family: the global edge label type is `ℕ` and the `n`-th box
is the single-vertex graph with loops `0, …, n`.  Vertex injections are the
unique maps `Fin 1 → Fin 1`, edge inclusion is monotonicity of `range`, and every
endpoint identity holds by subsingleton.  This shows the nesting data are
inhabited, so `exists_free_limit` is not a vacuous statement.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal NNReal

namespace FK.NestedMixture

/-- The one-vertex box with the first `n+1` parallel loops. -/
@[reducible] def loopBox (n : ℕ) : FK.InfiniteVolume.FiniteBox ℕ where
  Vertex := Fin 1
  edges := Finset.range (n + 1)
  source := fun _ => 0
  target := fun _ => 0

def loopBox_nest (n m : ℕ) (hnm : n ≤ m) : NestedBox (loopBox n) (loopBox m) where
  edge_sub := by
    intro e he
    simp only [loopBox, Finset.mem_range] at he ⊢
    omega
  vert := fun _ => 0
  vert_inj := fun a b _ => Subsingleton.elim a b
  src := fun e => Subsingleton.elim _ _
  tgt := fun e => Subsingleton.elim _ _

/-- The one-vertex loop family is a genuine growing family. -/
def loopFamily : GrowingFamily ℕ where
  box := loopBox
  edges_mono := by
    intro n m hnm e he
    simp only [loopBox, Finset.mem_range] at he ⊢
    omega
  covers := by
    intro e
    refine ⟨e, ?_⟩
    simp only [loopBox, Finset.mem_range]
    omega
  nest := loopBox_nest

/-- The existence theorem applies to an actual growing family. -/
theorem loopFamily_has_limit :
    ∃ φ : ProbabilityMeasure (FK.InfiniteVolume.Configuration ℕ),
      ∃ (hq : 0 < (2 : NNReal)) (hp : (1 / 2 : NNReal) ≤ 1),
        FK.InfiniteVolume.IsFKLimit loopFamily.exh hq hp
          (fun n => (loopFamily.box n).graph.freeBoundary) φ := by
  obtain ⟨φ, hφ⟩ := loopFamily.exists_free_limit (q := 2) (p := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨φ, _, _, hφ⟩

end FK.NestedMixture

#print axioms FK.NestedMixture.loopFamily_has_limit
