import FK.NestedMixture.Limit

/-!
# A genuinely growing-vertex example: the path boxes

The global edge label type is `ℕ`; the `n`-th box is the path on `n+1` vertices
with edges `0, …, n-1`, where edge `i` joins the vertices `i` and `i+1`.  Both the
vertex set and the edge set grow with `n`, the inclusion maps preserve endpoints,
and the vertex map is the order embedding `Fin (n+1) → Fin (m+1)`.

This exhibits the geometric input of `GrowingFamily` for an actual growing chain
of simple graphs (not merely parallel loops), so the free finite-volume laws of
the path boxes have a genuine full-sequence weak limit at `q ≥ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal NNReal

namespace FK.NestedMixture

/-- The path box on `n+1` vertices with `n` edges. -/
@[reducible] def pathBox (n : ℕ) : FK.InfiniteVolume.FiniteBox ℕ where
  Vertex := Fin (n + 1)
  edges := Finset.range n
  source := fun i => ⟨i.1, Nat.lt_succ_of_lt (Finset.mem_range.mp i.2)⟩
  target := fun i => ⟨i.1 + 1, Nat.succ_lt_succ (Finset.mem_range.mp i.2)⟩

/-- The order embedding of vertices. -/
def pathVert {n m : ℕ} (hnm : n ≤ m) : Fin (n + 1) → Fin (m + 1) :=
  fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_succ hnm)⟩

theorem pathVert_injective {n m : ℕ} (hnm : n ≤ m) : Function.Injective (pathVert hnm) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin (m + 1) => x.val) h

/-- The nesting data of the path boxes. -/
def pathNest (n m : ℕ) (hnm : n ≤ m) : NestedBox (pathBox n) (pathBox m) where
  edge_sub := by
    intro e he
    simp only [pathBox, Finset.mem_range] at he ⊢
    omega
  vert := pathVert hnm
  vert_inj := pathVert_injective hnm
  src := by
    intro e
    apply Fin.ext
    rfl
  tgt := by
    intro e
    apply Fin.ext
    rfl

/-- The path boxes form a growing family whose vertices and edges both grow. -/
def pathFamily : GrowingFamily ℕ where
  box := pathBox
  edges_mono := by
    intro n m hnm e he
    simp only [pathBox, Finset.mem_range] at he ⊢
    omega
  covers := by
    intro e
    refine ⟨e + 1, ?_⟩
    simp only [pathBox, Finset.mem_range]
    omega
  nest := pathNest

/-- **Free finite-volume limits of the path boxes**: a genuine growing-vertex
weak limit at `q = 2`, `p = 1/2`. -/
theorem pathFamily_has_limit :
    ∃ φ : ProbabilityMeasure (FK.InfiniteVolume.Configuration ℕ),
      ∃ (hq : 0 < (2 : NNReal)) (hp : (1 / 2 : NNReal) ≤ 1),
        FK.InfiniteVolume.IsFKLimit pathFamily.exh hq hp
          (fun n => (pathFamily.box n).graph.freeBoundary) φ := by
  obtain ⟨φ, hφ⟩ := pathFamily.exists_free_limit (q := 2) (p := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨φ, _, _, hφ⟩

end FK.NestedMixture

#print axioms FK.NestedMixture.pathFamily_has_limit
