/-
Part of the FK formalization campaign (member m8, direction d8).

# The random-cluster (FK) weight is log-supermodular for `q ≥ 1`

For a finite edge set `E` with an endpoint map into a finite vertex type `V`,
we package the cluster count of an open-edge set as the *corank* of the span of
the `ZMod 2`-edge vectors (`clusterCount S = |V| - rank`).  For a genuine graph this
is the number of connected components of the open subgraph including isolated
vertices; what the FKG theorem actually needs is its supermodularity

  `clusterCount (S ∪ T) + clusterCount (S ∩ T) ≥ clusterCount S + clusterCount T`

(the submodularity of the graphic rank), which is proved here from
`Submodule.finrank_sup_add_finrank_inf_eq`.  Feeding this into the lattice
condition gives that the random-cluster weight

  `ω ↦ c ^ |ω| · q ^ clusterCount ω`

is log-supermodular when `q ≥ 1`, hence positively associated by the FKG
theorem, and log-submodular when `q ≤ 1`.
-/
import FK.FKG.General

set_option linter.unusedSectionVars false

namespace FinFKG

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Open-edge sets -/

/-- The set of open edges of a bond configuration. -/
def openSet (ω : E → Bool) : Finset E := univ.filter fun e => ω e

@[simp] lemma mem_openSet {ω : E → Bool} {e : E} : e ∈ openSet ω ↔ ω e = true := by
  simp [openSet]

lemma openSet_sup (x y : E → Bool) : openSet (x ⊔ y) = openSet x ∪ openSet y := by
  ext e
  simp [openSet, Pi.sup_apply, Bool.or_eq_true]

lemma openSet_inf (x y : E → Bool) : openSet (x ⊓ y) = openSet x ∩ openSet y := by
  ext e
  simp [openSet, Pi.inf_apply, Bool.and_eq_true]

lemma openSet_le {x y : E → Bool} (h : x ≤ y) : openSet x ⊆ openSet y := by
  intro e he
  simp only [mem_openSet] at he ⊢
  by_contra hne
  have hx : x e = true := he
  have hy : y e = false := by simpa using hne
  have h' : x e ≤ y e := h e
  rw [hx, hy] at h'
  exact absurd h' (by decide)

/-! ### The `ZMod 2`-edge vectors and the cluster count -/

/-- The characteristic vector over `ZMod 2` of the two endpoints of an edge. -/
noncomputable def edgeVec (ends : E → V × V) (e : E) : V → ZMod 2 :=
  fun v => (if v = (ends e).1 then (1 : ZMod 2) else 0) +
    (if v = (ends e).2 then (1 : ZMod 2) else 0)

/-- The span of the edge vectors of the edges in `s`. -/
noncomputable def edgeSpan (ends : E → V × V) (s : Finset E) : Submodule (ZMod 2) (V → ZMod 2) :=
  Submodule.span (ZMod 2) ((fun e => edgeVec ends e) '' (s : Set E))

/-- The graphic rank of an open-edge set: the dimension of the span of its edge
vectors. -/
noncomputable def edgeRank (ends : E → V × V) (s : Finset E) : ℕ :=
  Module.finrank (ZMod 2) (edgeSpan ends s)

/-- The cluster count of an open-edge set: the corank of the span of its edge
vectors.  For a genuine graph this is the number of connected components of the
open subgraph, isolated vertices included. -/
noncomputable def clusterCount (ends : E → V × V) (s : Finset E) : ℕ :=
  Fintype.card V - edgeRank ends s

lemma edgeSpan_mono {ends : E → V × V} {s t : Finset E} (h : s ⊆ t) :
    edgeSpan ends s ≤ edgeSpan ends t := by
  refine Submodule.span_mono ?_
  rintro x ⟨e, he, rfl⟩
  exact ⟨e, h he, rfl⟩

lemma edgeSpan_union_le (ends : E → V × V) (s t : Finset E) :
    edgeSpan ends (s ∪ t) ≤ edgeSpan ends s ⊔ edgeSpan ends t := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨e, he, rfl⟩
  rw [Finset.mem_coe, Finset.mem_union] at he
  rcases he with h | h
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨e, by simpa using h, rfl⟩)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨e, by simpa using h, rfl⟩)

lemma edgeSpan_inter_le (ends : E → V × V) (s t : Finset E) :
    edgeSpan ends (s ∩ t) ≤ edgeSpan ends s ⊓ edgeSpan ends t := by
  refine le_inf (edgeSpan_mono (Finset.inter_subset_left ..))
    (edgeSpan_mono (Finset.inter_subset_right ..))

/-- Submodularity of the graphic rank. -/
theorem edgeRank_submodular (ends : E → V × V) (s t : Finset E) :
    edgeRank ends (s ∪ t) + edgeRank ends (s ∩ t) ≤ edgeRank ends s + edgeRank ends t := by
  have h1 := Submodule.finrank_mono (edgeSpan_union_le ends s t)
  have h2 := Submodule.finrank_mono (edgeSpan_inter_le ends s t)
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (edgeSpan ends s) (edgeSpan ends t)
  unfold edgeRank
  omega

/-- Supermodularity of the cluster count: the key combinatorial input for the
FKG lattice condition of the random-cluster weight. -/
theorem clusterCount_supermodular (ends : E → V × V) (s t : Finset E) :
    clusterCount ends s + clusterCount ends t ≤
      clusterCount ends (s ∪ t) + clusterCount ends (s ∩ t) := by
  have hsub := edgeRank_submodular ends s t
  have h1 : edgeRank ends (s ∪ t) ≤ Fintype.card V := by
    unfold edgeRank
    refine le_trans (Submodule.finrank_le _) ?_
    rw [Module.finrank_fintype_fun_eq_card]
  have h2 : edgeRank ends (s ∩ t) ≤ Fintype.card V := by
    unfold edgeRank
    refine le_trans (Submodule.finrank_le _) ?_
    rw [Module.finrank_fintype_fun_eq_card]
  have h3 : edgeRank ends s ≤ Fintype.card V := by
    unfold edgeRank
    refine le_trans (Submodule.finrank_le _) ?_
    rw [Module.finrank_fintype_fun_eq_card]
  have h4 : edgeRank ends t ≤ Fintype.card V := by
    unfold edgeRank
    refine le_trans (Submodule.finrank_le _) ?_
    rw [Module.finrank_fintype_fun_eq_card]
  unfold clusterCount
  omega

/-- Adding edges cannot increase the cluster count. -/
lemma clusterCount_antitone {ends : E → V × V} {s t : Finset E} (h : s ⊆ t) :
    clusterCount ends t ≤ clusterCount ends s := by
  have hmono : edgeRank ends s ≤ edgeRank ends t :=
    Submodule.finrank_mono (edgeSpan_mono h)
  unfold clusterCount
  omega

/-- With no open edge every vertex is its own cluster. -/
lemma clusterCount_empty (ends : E → V × V) : clusterCount ends ∅ = Fintype.card V := by
  have h : edgeSpan ends ∅ = ⊥ := by
    simp [edgeSpan]
  unfold clusterCount edgeRank
  rw [h]
  simp

/-- Sanity check that the rank-based cluster count behaves like a component
count: on the two-vertex graph with a single edge it equals `2` with no open
edge and `1` once the edge is open. -/
theorem clusterCount_two_vertex :
    clusterCount (V := Bool) (fun _ : Bool => (false, true)) (∅ : Finset Bool) = 2 ∧
      clusterCount (V := Bool) (fun _ : Bool => (false, true)) {true} = 1 := by
  constructor
  · rw [clusterCount_empty]
    simp
  · have hne : edgeVec (fun _ : Bool => (false, true)) true ≠ 0 := by
      intro h
      have h' := congrFun h false
      simp [edgeVec] at h'
    have himg : ((fun e => edgeVec (fun _ : Bool => (false, true)) e) ''
        (({true} : Finset Bool) : Set Bool))
        = {edgeVec (fun _ : Bool => (false, true)) true} := by
      simp
    have hrank : edgeRank (fun _ : Bool => (false, true)) {true} = 1 := by
      unfold edgeRank edgeSpan
      rw [himg]
      simpa using finrank_span_singleton (K := ZMod 2) hne
    unfold clusterCount
    rw [hrank]
    simp

/-- The random-cluster (FK) weight with edge-activity `c > 0` and cluster weight
`q > 0`, on the bond configurations of a finite graph given by `ends`. -/
noncomputable def fkWeight (c q : ℝ) (ends : E → V × V) (ω : E → Bool) : ℝ :=
  c ^ (openSet ω).card * q ^ (clusterCount ends (openSet ω))

lemma fkWeight_pos {c q : ℝ} (hc : 0 < c) (hq : 0 < q) (ends : E → V × V) (ω : E → Bool) :
    0 < fkWeight c q ends ω :=
  mul_pos (pow_pos hc _) (pow_pos hq _)

/-- The exponent bookkeeping of the FK weight: two factors combine
multiplicatively in the exponents. -/
theorem fkWeight_pair (a b : ℝ) (m1 m2 k1 k2 : ℕ) :
    (a ^ m1 * b ^ k1) * (a ^ m2 * b ^ k2) = a ^ (m1 + m2) * b ^ (k1 + k2) := by
  rw [mul_mul_mul_comm, ← pow_add, ← pow_add]

end FinFKG
