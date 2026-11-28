import FK.NestedTransportGeneral
import FK.SpecificationNesting

/-!
# Deleting vertex-only extensions with their induced boundary partition

If all edges of a finite labelled graph come from a vertex subgraph, then the
normalized FK law is unchanged by deleting all vertices outside that subgraph,
provided the boundary partition is pulled back. Components entirely outside
the subgraph depend only on the fixed boundary partition and cancel in the
normalization. No free-boundary hypothesis is used.
-/

open Set
open scoped Classical BigOperators ENNReal NNReal

namespace FK.IsolatedBoundaryTransport

open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.SpecificationNesting

variable {G H : LabelledMultigraph}

/-- Read a configuration on `H` in the edge coordinates of `G`. -/
noncomputable def pullConfig (eE : G.Edge ≃ H.Edge) : H.Configuration ≃ G.Configuration where
  toFun ω := ω ∘ eE
  invFun ω := ω ∘ eE.symm
  left_inv ω := by
    funext a
    exact congrArg ω (eE.apply_symm_apply a)
  right_inv ω := by
    funext a
    exact congrArg ω (eE.symm_apply_apply a)

@[simp] lemma pullConfig_apply (eE : G.Edge ≃ H.Edge)
    (ω : H.Configuration) (a : G.Edge) : pullConfig eE ω a = ω (eE a) := rfl

section Components

variable (f : G.Vertex → H.Vertex) (hf : Function.Injective f)
variable (eE : G.Edge ≃ H.Edge)
variable (hs : ∀ a, H.source (eE a) = f (G.source a))
variable (ht : ∀ a, H.target (eE a) = f (G.target a))
variable (β : H.BoundaryPartition)

/-- The fixed all-closed connection graph on the extending vertex type. -/
abbrev closedConnection : SimpleGraph H.Vertex :=
  H.connectionGraph β (fun _ => false)

lemma closed_adj_wired {u v : H.Vertex}
    (h : (closedConnection (H := H) β).Adj u v) : β.r u v := by
  rcases h.2 with hβ | ⟨a, ha, _⟩
  · exact hβ
  · exact Bool.noConfusion ha

lemma closed_reachable_wired {u v : H.Vertex}
    (h : (closedConnection (H := H) β).Reachable u v) : β.r u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact β.iseqv.refl _
  | tail _ huv ih => exact β.iseqv.trans ih (closed_adj_wired β huv)

section SourceRange
include eE hs
lemma source_mem_range (a : H.Edge) : H.source a ∈ Set.range f := by
  refine ⟨G.source (eE.symm a), ?_⟩
  have h := hs (eE.symm a)
  rw [eE.apply_symm_apply] at h
  exact h.symm
end SourceRange

section TargetRange
include eE ht
lemma target_mem_range (a : H.Edge) : H.target a ∈ Set.range f := by
  refine ⟨G.target (eE.symm a), ?_⟩
  have h := ht (eE.symm a)
  rw [eE.apply_symm_apply] at h
  exact h.symm
end TargetRange

section JoinsRange
include eE hs ht
lemma joins_mem_range {a : H.Edge} {u v : H.Vertex}
    (h : H.Joins a u v) : u ∈ Set.range f ∧ v ∈ Set.range f := by
  rcases h with h | h
  · rw [← h.1, ← h.2]
    exact ⟨source_mem_range f eE hs a, target_mem_range f eE ht a⟩
  · rw [← h.1, ← h.2]
    exact ⟨target_mem_range f eE ht a, source_mem_range f eE hs a⟩
end JoinsRange

section RegionIso
include hf hs ht
/-- The region graph of the extension is exactly the retained connection graph. -/
noncomputable def regionConnectionIso (ω : H.Configuration) :
    regionGraph (closedConnection (H := H) β) (H.connectionGraph β ω) (Set.range f) ≃g
      G.connectionGraph (Setoid.comap f β) (pullConfig eE ω) where
  toEquiv := (Equiv.ofInjective f hf).symm
  map_rel_iff' := by
    intro u v
    have hu : f ((Equiv.ofInjective f hf).symm u) = u.1 := by
      exact congrArg Subtype.val ((Equiv.ofInjective f hf).apply_symm_apply u)
    have hv : f ((Equiv.ofInjective f hf).symm v) = v.1 := by
      exact congrArg Subtype.val ((Equiv.ofInjective f hf).apply_symm_apply v)
    constructor
    swap
    · intro huv
      refine ⟨?_, ?_⟩
      · intro heq
        exact huv.1 ((Equiv.ofInjective f hf).symm.injective heq)
      · rcases huv.2 with hclosed | hopen
        · left
          change β.r (f ((Equiv.ofInjective f hf).symm u))
            (f ((Equiv.ofInjective f hf).symm v))
          rw [hu, hv]
          exact closed_reachable_wired β hclosed
        · rcases hopen.2 with hβ | ⟨a, ha, hjoin⟩
          · left
            change β.r (f ((Equiv.ofInjective f hf).symm u))
              (f ((Equiv.ofInjective f hf).symm v))
            rw [hu, hv]
            exact hβ
          · right
            refine ⟨eE.symm a, ?_, ?_⟩
            · change ω (eE (eE.symm a)) = true
              rwa [eE.apply_symm_apply]
            · rcases hjoin with h | h
              · apply Or.inl
                constructor <;> apply hf
                · have hsa := hs (eE.symm a)
                  rw [eE.apply_symm_apply] at hsa
                  exact hsa.symm.trans (h.1.trans hu.symm)
                · have hta := ht (eE.symm a)
                  rw [eE.apply_symm_apply] at hta
                  exact hta.symm.trans (h.2.trans hv.symm)
              · apply Or.inr
                constructor <;> apply hf
                · have hsa := hs (eE.symm a)
                  rw [eE.apply_symm_apply] at hsa
                  exact hsa.symm.trans (h.1.trans hv.symm)
                · have hta := ht (eE.symm a)
                  rw [eE.apply_symm_apply] at hta
                  exact hta.symm.trans (h.2.trans hu.symm)
    · intro huv
      have hne : u ≠ v := by
        intro heq
        apply huv.1
        rw [heq]
      have hne' : (u : H.Vertex) ≠ (v : H.Vertex) := by
        intro heq
        exact hne (Subtype.ext heq)
      refine ⟨hne, ?_⟩
      rcases huv.2 with hβ | ⟨a, ha, hjoin⟩
      · left
        apply SimpleGraph.Adj.reachable
        refine ⟨hne', Or.inl ?_⟩
        change β.r u.1 v.1
        rw [← hu, ← hv]
        exact hβ
      · right
        refine ⟨hne', Or.inr ⟨eE a, ?_, ?_⟩⟩
        · change ω (eE a) = true at ha
          exact ha
        · rcases hjoin with h | h
          · apply Or.inl
            constructor
            · rw [hs, h.1, hu]
            · rw [ht, h.2, hv]
          · apply Or.inr
            constructor
            · rw [hs, h.1, hv]
            · rw [ht, h.2, hu]

end RegionIso

lemma closed_le_connection (ω : H.Configuration) :
    closedConnection (H := H) β ≤ H.connectionGraph β ω := by
  apply H.connectionGraph_mono
  intro a
  exact bot_le

section AdjRange
include hs ht
lemma connection_adj_closed_or_mem_range (ω : H.Configuration)
    {u v : H.Vertex} (h : (H.connectionGraph β ω).Adj u v) :
    (closedConnection (H := H) β).Adj u v ∨ (u ∈ Set.range f ∧ v ∈ Set.range f) := by
  rcases h.2 with hβ | ⟨a, _, hjoin⟩
  · exact Or.inl ⟨h.1, Or.inl hβ⟩
  · exact Or.inr (joins_mem_range f eE hs ht hjoin)

end AdjRange

lemma not_meeting_iff_avoids (A : SimpleGraph H.Vertex) (R : Set H.Vertex)
    (C : A.ConnectedComponent) :
    (¬ ∃ x : R, A.connectedComponentMk (x : H.Vertex) = C) ↔
      ∀ v, v ∈ (C.supp : Set H.Vertex) → v ∈ Rᶜ := by
  constructor
  · intro h v hv hvR
    apply h
    refine ⟨⟨v, hvR⟩, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C v).mp hv
  · rintro h ⟨x, hx⟩
    have hmem : (x : H.Vertex) ∈ (C.supp : Set H.Vertex) :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C x.1).mpr hx
    exact h x.1 hmem x.2

/-- The number of fixed components wholly outside the retained vertex range. -/
noncomputable def deletedComponentCount : ℕ :=
  Nat.card {C : (closedConnection (H := H) β).ConnectedComponent //
    ¬ ∃ x : Set.range f, (closedConnection (H := H) β).connectedComponentMk (x : H.Vertex) = C}

section Count
include hf hs ht
/-- Components on the larger vertex type are retained components plus a fixed
number depending only on the boundary wiring outside the retained range. -/
theorem componentCount_pullConfig (ω : H.Configuration) :
    H.componentCount β ω =
      G.componentCount (Setoid.comap f β) (pullConfig eE ω) +
        deletedComponentCount f β := by
  let A := closedConnection (H := H) β
  let B := H.connectionGraph β ω
  let R := Set.range f
  let AR := regionGraph A B R
  let K := G.connectionGraph (Setoid.comap f β) (pullConfig eE ω)
  have hAB : A ≤ B := closed_le_connection β ω
  have hR : ∀ u v, B.Adj u v → A.Adj u v ∨ (u ∈ R ∧ v ∈ R) := by
    intro u v huv
    exact connection_adj_closed_or_mem_range f eE hs ht β ω huv
  have hmeet : Nat.card {C : B.ConnectedComponent //
      ∃ x : R, B.connectedComponentMk (x : H.Vertex) = C} =
      Nat.card AR.ConnectedComponent :=
    card_components_meeting B R AR (regionGraph_reachable_iff hAB hR)
  have hreg : Nat.card AR.ConnectedComponent = Nat.card K.ConnectedComponent := by
    exact Nat.card_congr (regionConnectionIso f hf eE hs ht β ω).connectedComponentEquiv
  have havoid : Nat.card {C : B.ConnectedComponent //
      ¬ ∃ x : R, B.connectedComponentMk (x : H.Vertex) = C} =
      Nat.card {C : A.ConnectedComponent //
        ¬ ∃ x : R, A.connectedComponentMk (x : H.Vertex) = C} := by
    rw [natCard_subtype_congr _ _ (not_meeting_iff_avoids B R),
      natCard_subtype_congr _ _ (not_meeting_iff_avoids A R)]
    apply card_components_avoiding_of_le hAB
    intro u v huv hout
    rcases hR u v huv with hA | ⟨hu, hv⟩
    · exact hA
    · rcases hout with hu' | hv'
      · exact (hu' hu).elim
      · exact (hv' hv).elim
  have hsplit := natCard_subtype_add B.ConnectedComponent
    (fun C : B.ConnectedComponent => ∃ x : R, B.connectedComponentMk (x : H.Vertex) = C)
  change Nat.card B.ConnectedComponent = Nat.card K.ConnectedComponent +
    Nat.card {C : A.ConnectedComponent //
      ¬ ∃ x : R, A.connectedComponentMk (x : H.Vertex) = C}
  rw [hsplit, hmeet, hreg, havoid]

end Count

end Components

section Weights

variable (f : G.Vertex → H.Vertex) (hf : Function.Injective f)
variable (eE : G.Edge ≃ H.Edge)
variable (hs : ∀ a, H.source (eE a) = f (G.source a))
variable (ht : ∀ a, H.target (eE a) = f (G.target a))
variable (β : H.BoundaryPartition)

lemma edgeWeight_pullConfig (p : NNReal) (ω : H.Configuration) :
    H.edgeWeight p ω = G.edgeWeight p (pullConfig eE ω) := by
  unfold LabelledMultigraph.edgeWeight
  rw [← Equiv.prod_comp eE (fun a : H.Edge => if ω a then p else 1 - p)]
  rfl

section Normalized
include hf hs ht
theorem fkWeight_pullConfig (q p : NNReal) (ω : H.Configuration) :
    H.fkWeight q p β ω =
      G.fkWeight q p (Setoid.comap f β) (pullConfig eE ω) *
        q ^ deletedComponentCount f β := by
  unfold LabelledMultigraph.fkWeight
  rw [componentCount_pullConfig f hf eE hs ht β, edgeWeight_pullConfig, pow_add]
  ring

theorem partitionFunction_pullConfig (q p : NNReal) :
    H.partitionFunction q p β =
      G.partitionFunction q p (Setoid.comap f β) * q ^ deletedComponentCount f β := by
  unfold LabelledMultigraph.partitionFunction
  rw [← Equiv.sum_comp (pullConfig eE)
    (fun ω : G.Configuration => G.fkWeight q p (Setoid.comap f β) ω), Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => fkWeight_pullConfig f hf eE hs ht β q p ω)

theorem fkPMF_pullConfig {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ω : H.Configuration) :
    H.fkPMF hq hp β ω = G.fkPMF hq hp (Setoid.comap f β) (pullConfig eE ω) := by
  rw [LabelledMultigraph.fkPMF_apply, LabelledMultigraph.fkPMF_apply,
    fkWeight_pullConfig f hf eE hs ht β, partitionFunction_pullConfig f hf eE hs ht β]
  have hc : q ^ deletedComponentCount f β ≠ 0 := pow_ne_zero _ hq.ne'
  rw [mul_div_mul_right _ _ hc]

/-- The normalized FK law pushes forward exactly under deletion of the
vertex-only extension, with the boundary partition pulled back. -/
theorem map_fkPMF_pullConfig {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    PMF.map (pullConfig eE) (H.fkPMF hq hp β) =
      G.fkPMF hq hp (Setoid.comap f β) := by
  apply PMF.ext
  intro ω
  rw [PMF.map_apply]
  let z := (pullConfig eE).symm ω
  rw [tsum_eq_single z]
  · simp only [show ω = pullConfig eE z by simp [z], if_pos]
    exact fkPMF_pullConfig f hf eE hs ht β hq hp z
  · intro z' hz'
    have hne : ω ≠ pullConfig eE z' := by
      intro h
      apply hz'
      apply (pullConfig eE).injective
      simpa [z] using h.symm
    simp [hne]

end Normalized

end Weights

end FK.IsolatedBoundaryTransport

#print axioms FK.IsolatedBoundaryTransport.componentCount_pullConfig
#print axioms FK.IsolatedBoundaryTransport.map_fkPMF_pullConfig
