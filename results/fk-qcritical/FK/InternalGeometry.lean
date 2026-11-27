import FK.ExternalRoot

noncomputable section

open scoped Classical
open CurvatureVariance.Infra.Percolation
open Set

namespace FK.BurtonKeane
open FK.ClusterCover

universe u
variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- Actual graph edges with both endpoints in `U`. -/
def internal (G : SimpleGraph V) (U : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∀ x ∈ e, x ∈ U}

/-- The actual graph edges internal to `U`, as a subtype of the configuration
coordinates. -/
def internalSet (G : SimpleGraph V) (U : Set V) : Set G.edgeSet :=
  {e | (e : Sym2 V) ∈ internal G U}

/-- Open all and only the internal edges of `U`. -/
def openInternal (U : Set V) (ω : G.edgeSet → Bool) : G.edgeSet → Bool :=
  fun e => if (e : Sym2 V) ∈ internal G U then true else ω e

lemma openInternal_of_notMem {U : Set V} (e : G.edgeSet)
    (he : (e : Sym2 V) ∉ internal G U) : openInternal U ω e = ω e := by
  simp [openInternal, he]

lemma openInternal_of_mem {U : Set V} (e : G.edgeSet)
    (he : (e : Sym2 V) ∈ internal G U) : openInternal U ω e = true := by
  simp [openInternal, he]

lemma internal_subset_incidence (G : SimpleGraph V) {U : Set V} :
    internal G U ⊆ incidence G U := by
  intro e he
  rcases he with ⟨heG, hU⟩
  induction e using Sym2.ind with
  | _ a b => exact ⟨heG, a, hU a (by simp), by simp⟩

lemma finite_internalSet [G.LocallyFinite] {U : Set V} (hU : U.Finite) :
    (internalSet G U).Finite := by
  have hInt : (internal G U).Finite :=
    (finite_incidence hU).subset (internal_subset_incidence G)
  exact hInt.preimage Subtype.val_injective.injOn

/-- The finite coordinate set on which `openInternal` forces edges open. -/
noncomputable def internalFinset [G.LocallyFinite] {U : Set V} (hU : U.Finite) :
    Finset G.edgeSet := (finite_internalSet (G := G) hU).toFinset

lemma openInternal_eq_of_notMem_incidence' {U : Set V} (e : G.edgeSet)
    (he : (e : Sym2 V) ∉ incidence G U) : openInternal U ω e = ω e := by
  apply openInternal_of_notMem
  intro hi
  exact he (internal_subset_incidence G hi)

/-- Internal opening preserves every incident-avoiding walk exactly. -/
lemma isOpenIn_openInternal_of_avoidIncidence {U : Set V} {a b : V}
    (p : G.Walk a b) (hp : IsOpenIn ω (Set.univ \ incidence G U) p) :
    IsOpenIn (openInternal U ω) (Set.univ \ incidence G U) p := by
  intro d hd
  have h := hp d hd
  refine ⟨h.1, ?_⟩
  have he : d.edge ∉ incidence G U := by
    intro hi
    exact h.1.2 hi
  rw [openInternal_eq_of_notMem_incidence' (ω := ω) (U := U) (e := ⟨d.edge, d.edge_mem⟩) he]
  exact h.2

/-- Opening internal edges is idempotent: a second application leaves every
coordinate unchanged. -/
@[simp] lemma openInternal_idem (U : Set V) (ω : G.edgeSet → Bool) :
    openInternal U (openInternal U ω) = openInternal U ω := by
  funext e
  by_cases he : (e : Sym2 V) ∈ internal G U <;> simp [openInternal, he]

lemma le_openInternal {U : Set V} (ω : G.edgeSet → Bool) : ω ≤ openInternal U ω := by
  intro e
  by_cases he : (e : Sym2 V) ∈ internal G U
  · rw [openInternal_of_mem (ω := ω) (U := U) e he]
    exact Bool.le_true _
  · rw [openInternal_of_notMem (ω := ω) (U := U) e he]

/-- Internal opening is exactly the finite patch forcing every internal edge
to `true`. -/
lemma openInternal_eq_updateFinset [G.LocallyFinite] {U : Set V} (hU : U.Finite) :
    openInternal U ω = @Function.updateFinset G.edgeSet (fun _ => Bool)
      (fun a b => Classical.propDecidable (a = b)) ω
      (internalFinset (G := G) hU) (fun _ => true) := by
  funext e
  by_cases he : e ∈ internalFinset (G := G) hU
  · have heI : (e : Sym2 V) ∈ internal G U := by
      simpa only [internalFinset, Set.Finite.mem_toFinset, internalSet,
        Set.mem_ofPred_eq] using he
    rw [openInternal_of_mem e heI]
    simp only [Function.updateFinset, he, dite_true]
  · have heI : (e : Sym2 V) ∉ internal G U := by
      simpa only [internalFinset, Set.Finite.mem_toFinset, internalSet,
        Set.mem_ofPred_eq] using he
    rw [openInternal_of_notMem e heI]
    simp only [Function.updateFinset, he, dite_false]


/-- Transfer avoiding nonconnection to an earlier root by composing with
avoiding attachment links. -/
lemma avoiding_nonConnected_trans {A : Set (Sym2 V)} {x y : V}
    (hx : OpenConnected G ω (Set.univ \ A) x y) {z : V}
    (hfree : ¬ OpenConnected G ω (Set.univ \ A) y z) {u : V}
    (hu : OpenConnected G ω (Set.univ \ A) z u) :
    ¬ OpenConnected G ω (Set.univ \ A) x u := by
  intro h
  obtain ⟨q, hq⟩ := h
  apply hfree
  obtain ⟨q0, hq0⟩ := hx
  obtain ⟨q1, hq1⟩ := hu
  exact ⟨q0.reverse.append (q.append q1.reverse),
    isOpenIn_append.mpr ⟨isOpenIn_reverse q0 hq0,
      isOpenIn_append.mpr ⟨hq, isOpenIn_reverse q1 hq1⟩⟩⟩
