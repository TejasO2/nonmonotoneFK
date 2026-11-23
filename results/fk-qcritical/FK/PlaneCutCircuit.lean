import FK.PlanarMatroid

/-!
# Cut/circuit duality for finite labelled plane-dual pairs

This file proves the finite interface step following graphic matroid duality:
every edge of an arbitrary vertex cut belongs to a circuit of the face-dual
cycle matroid contained in that cut. The construction uses a spanning forest
of the complement of the cut and a fundamental cocircuit.

No planarity is asserted for an arbitrary labelled multigraph. An actual
`GraphicDualCertificate` is required for the dual pair. Nor is a matroid
circuit identified with a topological Jordan curve; that identification is a
separate plane-embedding theorem.
-/

namespace FK.Finite.LabelledMultigraph

open scoped Classical
open Matroid

variable (G : LabelledMultigraph)

/-- The labelled edge cut of a set of vertices. Loops never belong to it and
parallel labels are retained independently. -/
def vertexCut (S : Set G.Vertex) : Set G.Edge :=
  {e | (G.source e ∈ S ∧ G.target e ∉ S) ∨
    (G.source e ∉ S ∧ G.target e ∈ S)}

lemma notMem_vertexCut_of_mem_of_mem {S : Set G.Vertex} {e : G.Edge}
    (hs : G.source e ∈ S) (ht : G.target e ∈ S) : e ∉ G.vertexCut S := by
  simp [vertexCut, hs, ht]

lemma notMem_vertexCut_of_notMem_of_notMem {S : Set G.Vertex} {e : G.Edge}
    (hs : G.source e ∉ S) (ht : G.target e ∉ S) : e ∉ G.vertexCut S := by
  simp [vertexCut, hs, ht]

lemma source_ne_target_of_mem_vertexCut {S : Set G.Vertex} {e : G.Edge}
    (he : e ∈ G.vertexCut S) : G.source e ≠ G.target e := by
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact fun h => ht (h ▸ hs)
  · exact fun h => hs (h ▸ ht)

/-- Membership of a vertex set propagates along a walk whose labelled edges
avoid its cut. -/
lemma target_mem_of_walk_compl_vertexCut {S : Set G.Vertex} {u v : G.Vertex}
    (w : (G.connectionGraph G.freeBoundary
      (G.setConfig (Set.univ \ G.vertexCut S))).Walk u v)
    (hu : u ∈ S) : v ∈ S := by
  induction w with
  | nil => exact hu
  | @cons u v w huv w ih =>
      apply ih
      rcases huv.2 with hfree | ⟨e, he, hjoin⟩
      · exact (huv.1 hfree).elim
      · have hecut : e ∉ G.vertexCut S := by
          have : e ∈ Set.univ \ G.vertexCut S := by
            simpa [setConfig] using he
          exact this.2
        rcases hjoin with ⟨hes, het⟩ | ⟨het, hes⟩
        · by_contra hv
          exact hecut (Or.inl ⟨by rwa [hes], by rwa [het]⟩)
        · by_contra hv
          exact hecut (Or.inr ⟨by rwa [het], by rwa [hes]⟩)

lemma not_reachable_compl_vertexCut {S : Set G.Vertex} {e : G.Edge}
    (he : e ∈ G.vertexCut S) :
    ¬ (G.connectionGraph G.freeBoundary
      (G.setConfig (Set.univ \ G.vertexCut S))).Reachable
        (G.source e) (G.target e) := by
  intro h
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ht (G.target_mem_of_walk_compl_vertexCut h.some hs)
  · exact hs (G.target_mem_of_walk_compl_vertexCut h.symm.some ht)

/-- Removing a nonempty vertex cut is not spanning in the cycle matroid. -/
lemma not_spanning_compl_vertexCut {S : Set G.Vertex} {e : G.Edge}
    (he : e ∈ G.vertexCut S) :
    ¬ G.cycleMatroid.Spanning (G.cycleMatroid.E \ G.vertexCut S) := by
  intro hspan
  obtain ⟨B, hB, hBsub⟩ := hspan.exists_isBase_subset
  have hbasis : G.cycleMatroid.IsBasis B Set.univ := by
    simpa using hB.isBasis_ground
  have hne : G.source e ≠ G.target e := G.source_ne_target_of_mem_vertexCut he
  have hopen : (G.connectionGraph G.freeBoundary G.allOpen).Reachable
      (G.source e) (G.target e) := by
    apply SimpleGraph.Adj.reachable
    refine ⟨hne, Or.inr ⟨e, rfl, ?_⟩⟩
    exact Or.inl ⟨rfl, rfl⟩
  have hreachB := (G.reachable_setConfig_iff_of_isBasis hbasis
    (G.source e) (G.target e)).mpr (by simpa [setConfig, allOpen] using hopen)
  have hle : G.connectionGraph G.freeBoundary (G.setConfig B) ≤
      G.connectionGraph G.freeBoundary
        (G.setConfig (Set.univ \ G.vertexCut S)) := by
    apply G.connectionGraph_mono
    apply G.setConfig_mono
    simpa using hBsub
  exact G.not_reachable_compl_vertexCut he (hreachB.mono hle)

/-- If a vertex set is a union of components of the open graph, every edge of
its cut is closed. -/
def OpenComponentSaturated (ω : G.Configuration) (S : Set G.Vertex) : Prop :=
  ∀ e, ω e = true → (G.source e ∈ S ↔ G.target e ∈ S)

lemma closed_of_mem_vertexCut_of_openComponentSaturated {ω : G.Configuration}
    {S : Set G.Vertex} (hS : G.OpenComponentSaturated ω S)
    {e : G.Edge} (he : e ∈ G.vertexCut S) : ω e = false := by
  apply Bool.eq_false_iff.mpr
  intro hopen
  have h := hS e hopen
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ht (h.mp hs)
  · exact hs (h.mpr ht)

end FK.Finite.LabelledMultigraph

namespace FK.Finite.PlaneMatroid.LabelledDualPair

open scoped Classical
open Matroid
open FK.Finite.LabelledMultigraph
open FK.Configuration

variable (P : LabelledDualPair)

/-- Every edge of a primal vertex cut lies on a cocircuit of the primal cycle
matroid contained in that cut. -/
theorem exists_isCocircuit_subset_vertexCut {S : Set P.Vertex} {e : P.Edge}
    (he : e ∈ P.primal.vertexCut S) :
    ∃ C, C ⊆ P.primal.vertexCut S ∧ e ∈ C ∧
      P.primal.cycleMatroid.IsCocircuit C := by
  let M := P.primal.cycleMatroid
  let K := M.E \ P.primal.vertexCut S
  obtain ⟨B₀, hB₀⟩ := M.exists_isBasis K
  have heB₀ : e ∉ B₀ := by
    intro heB
    exact (hB₀.subset heB).2 he
  have hecl : e ∉ M.closure B₀ := by
    intro hecl
    have hcases := hB₀.indep.mem_closure_iff.mp hecl
    rcases hcases with hdep | heB
    · have hreach : (P.primal.connectionGraph P.primal.freeBoundary
          (P.primal.setConfig B₀)).Reachable
            (P.primal.source e) (P.primal.target e) := by
        apply P.primal.reachable_of_not_isOpenForest_insert
          ((P.primal.cycleMatroid_indep B₀).mp hB₀.indep) heB₀
        exact (P.primal.cycleMatroid_indep (insert e B₀)).not.mp hdep.1
      have hle : P.primal.connectionGraph P.primal.freeBoundary
          (P.primal.setConfig B₀) ≤
          P.primal.connectionGraph P.primal.freeBoundary
            (P.primal.setConfig (Set.univ \ P.primal.vertexCut S)) := by
        apply P.primal.connectionGraph_mono
        apply P.primal.setConfig_mono
        simpa [K, M] using hB₀.subset
      exact P.primal.not_reachable_compl_vertexCut he (hreach.mono hle)
    · exact heB₀ heB
  have hinsert : M.Indep (insert e B₀) :=
    (hB₀.indep.notMem_closure_iff_of_notMem heB₀ (Set.mem_univ e)).mp hecl
  obtain ⟨B, hB, heB⟩ := hinsert.exists_isBase_superset
  let C := M.fundCocircuit e B
  have heBmem : e ∈ B := heB (Set.mem_insert e B₀)
  have hB₀sub : B₀ ⊆ B \ {e} := by
    intro f hf
    refine ⟨heB (Set.mem_insert_of_mem e hf), ?_⟩
    intro hfe
    subst f
    exact heB₀ hf
  refine ⟨C, ?_, M.mem_fundCocircuit e B,
    Matroid.fundCocircuit_isCocircuit heBmem hB⟩
  intro f hfC
  have hf := M.fundCocircuit_subset_insert_compl e B hfC
  rcases hf with rfl | hf
  · exact he
  · by_contra hfcut
    have hfK : f ∈ K := by
      simp only [K, Set.mem_sdiff]
      exact ⟨hf.1, hfcut⟩
    have hfcl₀ : f ∈ M.closure B₀ := hB₀.subset_closure hfK
    have hfcl : f ∈ M.closure (B \ {e}) :=
      M.closure_subset_closure hB₀sub hfcl₀
    have hfdep : M.Dep (insert f (B \ {e})) := by
      rcases (hB.indep.sdiff {e}).mem_closure_iff.mp hfcl with hdep | hfmem
      · exact hdep
      · exact (hf.2 hfmem.1).elim
    have hfe : f ≠ e := by
      intro hfe
      subst f
      exact hf.2 heBmem
    have hfind : M.Indep (insert f B \ {e}) := by
      have hfund : e ∈ M.fundCircuit f B :=
        (hB.mem_fundCocircuit_iff_mem_fundCircuit).mp hfC
      exact (hB.indep.mem_fundCircuit_iff
        (by rw [hB.closure_eq]; simp [M]) hf.2).mp hfund
    apply hfdep.1
    have heq : insert f (B \ {e}) = insert f B \ {e} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_sdiff]
      aesop
    rw [heq]
    exact hfind

/-- The same cut/circuit statement on the actual face-dual graph. -/
theorem exists_faceDual_isCircuit_subset_vertexCut
    (_hP : P.GraphicDualCertificate) {S : Set P.Vertex} {e : P.Edge}
    (he : e ∈ P.primal.vertexCut S) :
    ∃ C, C ⊆ P.primal.vertexCut S ∧ e ∈ C ∧
      P.faceDual.cycleMatroid.IsCircuit C := by
  obtain ⟨C, hC, heC, hco⟩ := P.exists_isCocircuit_subset_vertexCut he
  refine ⟨C, hC, heC, ?_⟩
  rw [← _hP.dual_cycleMatroid]
  exact hco

/-- **Finite interface circuits.** For a union of primal open components,
each edge of its boundary belongs to a dual circuit consisting entirely of
primal-closed (equivalently dual-open) labels. -/
theorem exists_dualOpen_isCircuit_subset_vertexCut
    (hP : P.GraphicDualCertificate) (ω : P.primal.Configuration)
    {S : Set P.Vertex} (hS : P.primal.OpenComponentSaturated ω S)
    {e : P.Edge} (he : e ∈ P.primal.vertexCut S) :
    ∃ C, C ⊆ P.primal.vertexCut S ∧ e ∈ C ∧
      P.faceDual.cycleMatroid.IsCircuit C ∧
      C ⊆ P.faceDual.openEdgeSet (dualConfig (Equiv.refl P.Edge) ω) := by
  obtain ⟨C, hCcut, heC, hC⟩ := P.exists_faceDual_isCircuit_subset_vertexCut hP he
  refine ⟨C, hCcut, heC, hC, ?_⟩
  intro f hf
  have hfclosed : ω f = false :=
    P.primal.closed_of_mem_vertexCut_of_openComponentSaturated hS (hCcut hf)
  change (dualConfig (Equiv.refl P.Edge) ω f) = true
  change (!ω f) = true
  simp [hfclosed]

end FK.Finite.PlaneMatroid.LabelledDualPair

namespace FK.Finite.LabelledMultigraph

open scoped Classical
open Matroid

variable (G : LabelledMultigraph)

/-- The vertex set of the actual open component through `x`, with no boundary
wiring and with the ambient isolated vertices retained. -/
def openVertexComponent (ω : G.Configuration) (x : G.Vertex) : Set G.Vertex :=
  {y | (G.connectionGraph G.freeBoundary ω).Reachable x y}

lemma openComponentSaturated_openVertexComponent (ω : G.Configuration)
    (x : G.Vertex) : G.OpenComponentSaturated ω (G.openVertexComponent ω x) := by
  intro e he
  by_cases hst : G.source e = G.target e
  · simp only [openVertexComponent, Set.mem_ofPred_eq, hst]
  · have hadj : (G.connectionGraph G.freeBoundary ω).Adj
        (G.source e) (G.target e) :=
      ⟨hst, Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩⟩
    constructor
    · intro hs
      exact hs.trans hadj.reachable
    · intro ht
      exact ht.trans hadj.symm.reachable

/-- Every label of a cycle-matroid circuit has its ends connected after that
label alone is deleted from the circuit. This includes singleton loop circuits
and two-label parallel circuits. -/
lemma reachable_sdiff_singleton_of_cycleMatroid_isCircuit {C : Set G.Edge}
    (hC : G.cycleMatroid.IsCircuit C) {e : G.Edge} (he : e ∈ C) :
    (G.connectionGraph G.freeBoundary (G.setConfig (C \ {e}))).Reachable
      (G.source e) (G.target e) :=
  G.reachable_of_mem_diff_of_isBasis (hC.sdiff_singleton_isBasis he)
    ⟨he, by simp⟩

end FK.Finite.LabelledMultigraph

namespace FK.Finite.PlaneMatroid.LabelledDualPair

open scoped Classical
open Matroid
open FK.Finite.LabelledMultigraph
open FK.Configuration

variable (P : LabelledDualPair)

/-- Boundary of an actual primal open component: every chosen boundary label
lies on a dual-open circuit, and every label of that circuit has its face
endpoints connected by precisely the remaining circuit labels. -/
theorem exists_dualOpen_circuit_boundary_openComponent
    (hP : P.GraphicDualCertificate) (ω : P.primal.Configuration) (x : P.Vertex)
    {e : P.Edge} (he : e ∈ P.primal.vertexCut (P.primal.openVertexComponent ω x)) :
    ∃ C, C ⊆ P.primal.vertexCut (P.primal.openVertexComponent ω x) ∧ e ∈ C ∧
      P.faceDual.cycleMatroid.IsCircuit C ∧
      C ⊆ P.faceDual.openEdgeSet (dualConfig (Equiv.refl P.Edge) ω) ∧
      ∀ f ∈ C,
        (P.faceDual.connectionGraph P.faceDual.freeBoundary
          (P.faceDual.setConfig (C \ {f}))).Reachable
            (P.faceDual.source f) (P.faceDual.target f) := by
  obtain ⟨C, hCcut, heC, hC, hCopen⟩ :=
    P.exists_dualOpen_isCircuit_subset_vertexCut hP ω
      (P.primal.openComponentSaturated_openVertexComponent ω x) he
  refine ⟨C, hCcut, heC, hC, hCopen, ?_⟩
  intro f hf
  exact P.faceDual.reachable_sdiff_singleton_of_cycleMatroid_isCircuit hC hf

end FK.Finite.PlaneMatroid.LabelledDualPair
