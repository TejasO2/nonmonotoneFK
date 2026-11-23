import FK.PlanarMatroid
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Binary cellular geometry for labelled plane multigraphs

The graph underlying these constructions is never replaced by a simple graph.
Loops and parallel labelled edges are retained.  The eventual cellular input
will consist of face-boundary chains, the chain relation, and exactness at the
edge module; no matroid-duality equality is an input.
-/

namespace FK.Finite.Cellular

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional
open FK.FinitePlane FK.Finite.PlaneMatroid

/-- The binary endpoint chain of an oriented labelled edge.  Orientation is
immaterial over `ZMod 2`; in particular, every loop has zero boundary. -/
def edgeBoundary {V E : Type*} [Fintype V] [DecidableEq V]
    (source target : E → V) (e : E) : V → ZMod 2 :=
  Pi.single (source e) 1 + Pi.single (target e) 1

end FK.Finite.Cellular

namespace FK.Finite.LabelledMultigraph

attribute [local instance] Classical.propDecidable

open FK.Finite.Cellular
open FK.Finite.Conditional

variable (G : LabelledMultigraph)

/-- The unsigned binary endpoint vector of a labelled edge. -/
noncomputable def boundary (e : G.Edge) : G.Vertex → ZMod 2 := by
  classical
  exact edgeBoundary G.source G.target e

lemma boundary_apply (e : G.Edge) (v : G.Vertex) :
    G.boundary e v = (if G.source e = v then 1 else 0) +
      (if G.target e = v then 1 else 0) := by
  classical
  simp [boundary, edgeBoundary, Pi.single_apply, eq_comm]

@[simp] lemma boundary_loop (e : G.Edge) (h : G.source e = G.target e) :
    G.boundary e = 0 := by
  classical
  ext v
  by_cases ht : G.target e = v <;>
    simp [boundary_apply, h, ht, ZModModule.add_self]

lemma boundary_comm (e : G.Edge) :
    edgeBoundary G.source G.target e = edgeBoundary G.target G.source e := by
  classical
  exact add_comm _ _

/-- A path using labels in `A` telescopes to the binary endpoint chain of
its endpoints.  This chooses a labelled edge for every graph adjacency; it
never identifies parallel labels. -/
lemma vertexChain_add_mem_span_boundary_of_reachable {A : Set G.Edge}
    {u v : G.Vertex}
    (h : (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable u v) :
    (Pi.single u 1 : G.Vertex → ZMod 2) + Pi.single v 1 ∈
      Submodule.span (ZMod 2) (G.boundary '' A) := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
      rw [ZModModule.add_self]
      exact Submodule.zero_mem _
  | @cons u w v huv p ih =>
      have huvedges : ∃ e, G.setConfig A e = true ∧ G.Joins e u w := by
        rcases huv.2 with hfree | hedge
        · exact (huv.1 hfree).elim
        · exact hedge
      have hmem : G.boundary (Classical.choose huvedges) ∈
          Submodule.span (ZMod 2) (G.boundary '' A) := by
        apply Submodule.subset_span
        refine ⟨Classical.choose huvedges, ?_, rfl⟩
        have ha := (Classical.choose_spec huvedges).1
        simpa [setConfig] using ha
      have hjoin := (Classical.choose_spec huvedges).2
      have hedge : G.boundary (Classical.choose huvedges) =
          (Pi.single u 1 : G.Vertex → ZMod 2) + Pi.single w 1 := by
        rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · simp [boundary, edgeBoundary, hs, ht]
        · simp [boundary, edgeBoundary, hs, ht, add_comm]
      have hsum := Submodule.add_mem _ hmem ih
      rw [hedge] at hsum
      simpa only [ZModModule.add_add_add_cancel] using hsum


/-- Evaluation pairing with a vertex potential. -/
noncomputable def pairingLinear {V : Type*} [Fintype V] (x : V → ZMod 2) :
    Module.Dual (ZMod 2) (V → ZMod 2) := by
  classical
  exact dotProductEquiv (ZMod 2) V x

lemma pairingLinear_apply {V : Type*} [Fintype V] (x y : V → ZMod 2) :
    pairingLinear x y = dotProduct x y := by
  classical
  exact dotProductEquiv_apply_apply (ZMod 2) V x y

lemma dotProduct_boundary (x : G.Vertex → ZMod 2) (e : G.Edge) :
    dotProduct x (G.boundary e) = x (G.source e) + x (G.target e) := by
  classical
  simp [boundary, edgeBoundary, dotProduct_add, dotProduct_single_one]

/-- The endpoint boundary of a label outside a component cannot be generated
by boundaries of labels inside that component's edge set. -/
lemma boundary_notMem_span_of_not_reachable {A : Set G.Edge} {e : G.Edge}
    (heA : ∀ a ∈ A,
      (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable
        (G.source a) (G.target a))
    (hne : ¬ (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable
      (G.source e) (G.target e)) :
    G.boundary e ∉ Submodule.span (ZMod 2) (G.boundary '' A) := by
  classical
  let H := G.connectionGraph G.freeBoundary (G.setConfig A)
  let x : G.Vertex → ZMod 2 := fun v => if H.Reachable (G.source e) v then 1 else 0
  let L : Module.Dual (ZMod 2) (G.Vertex → ZMod 2) := pairingLinear x
  have hgen : ∀ a ∈ A, L (G.boundary a) = 0 := by
    intro a ha
    have hreach : H.Reachable (G.source e) (G.source a) ↔
        H.Reachable (G.source e) (G.target a) := by
      constructor <;> intro h
      · exact h.trans (heA a ha)
      · exact h.trans (heA a ha).symm
    rw [pairingLinear_apply, dotProduct_boundary]
    have hx : x (G.source a) = x (G.target a) := by simp only [x, hreach]
    rw [hx]
    exact ZModModule.add_self _
  have hspan : Submodule.span (ZMod 2) (G.boundary '' A) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro y ⟨a, ha, rfl⟩
    exact hgen a ha
  intro hmem
  have hz := hspan hmem
  change L (G.boundary e) = 0 at hz
  rw [pairingLinear_apply, dotProduct_boundary] at hz
  have hs : x (G.source e) = 1 := by simp [x, H]
  have ht : x (G.target e) = 0 := by simp [x, hne, H]
  rw [hs, ht] at hz
  exact one_ne_zero hz

/-- Exact span characterization of connection by a prescribed set of labelled
edges. -/
lemma boundary_mem_span_iff_reachable {A : Set G.Edge} {e : G.Edge} :
    G.boundary e ∈ Submodule.span (ZMod 2) (G.boundary '' A) ↔
      (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable
        (G.source e) (G.target e) := by
  constructor
  · intro hmem
    by_contra hne
    have hall : ∀ a ∈ A,
        (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable
          (G.source a) (G.target a) := by
      intro a ha
      by_cases hst : G.source a = G.target a
      · simpa [hst] using
          (SimpleGraph.Reachable.refl
            (G.connectionGraph G.freeBoundary (G.setConfig A)) (G.source a))
      · apply SimpleGraph.Adj.reachable
        refine ⟨hst, Or.inr ⟨a, ?_, Or.inl ⟨rfl, rfl⟩⟩⟩
        simp [setConfig, ha]
    exact G.boundary_notMem_span_of_not_reachable hall hne hmem
  · intro h
    have hchain := G.vertexChain_add_mem_span_boundary_of_reachable h
    simpa only [boundary, edgeBoundary, ZModModule.sub_eq_add] using hchain


lemma endpointsConnectedWithout_setConfig (A : Set G.Edge) (e : G.Edge) :
    endpointsConnectedWithout G G.freeBoundary e (G.setConfig A) ↔
      (G.connectionGraph G.freeBoundary (G.setConfig (A \ {e}))).Reachable
        (G.source e) (G.target e) := by
  unfold endpointsConnectedWithout
  rw [G.withEdge_false_setConfig]

/-- The cycle matroid's independent sets are exactly the linearly independent
sets of binary incidence vectors.  The statement is on the original labelled
edge type, so it includes loops and parallel edges. -/
theorem isForestSet_iff_linearIndepOn (A : Set G.Edge) :
    G.IsForestSet A ↔ LinearIndepOn (ZMod 2) G.boundary A := by
  rw [linearIndepOn_iff_notMem_span]
  constructor
  · intro h e heA
    rw [G.boundary_mem_span_iff_reachable]
    intro hreach
    exact h e (by simp [IsForestSet, setConfig, heA])
      ((G.endpointsConnectedWithout_setConfig A e).mpr hreach)
  · intro h e he hconn
    have heA : e ∈ A := by simpa [setConfig] using he
    have hreach := (G.endpointsConnectedWithout_setConfig A e).mp hconn
    exact h e heA ((G.boundary_mem_span_iff_reachable).mpr hreach)

/-- Binary representability of the existing labelled cycle matroid, stated by
an exact independence characterization rather than by a new abstract matroid. -/
theorem cycleMatroid_indep_iff_linearIndepOn (A : Set G.Edge) :
    (G.cycleMatroid).Indep A ↔ LinearIndepOn (ZMod 2) G.boundary A := by
  rw [G.cycleMatroid_indep]
  exact G.isForestSet_iff_linearIndepOn A

end FK.Finite.LabelledMultigraph

namespace FK.Finite.LabelledMultigraph

attribute [local instance] Classical.propDecidable

open FK.Finite.Cellular

/-- Matrix of unsigned binary endpoint chains, with actual labelled edges as
columns. -/
noncomputable def boundaryMatrix (G : LabelledMultigraph) :
    Matrix G.Vertex G.Edge (ZMod 2) := fun v e => G.boundary e v

/-- The simplicial boundary map `C₁(G;F₂) → C₀(G;F₂)`. -/
noncomputable def boundaryMap (G : LabelledMultigraph) :
    (G.Edge → ZMod 2) →ₗ[ZMod 2] (G.Vertex → ZMod 2) :=
  Matrix.mulVecLin G.boundaryMatrix

@[simp] lemma boundaryMap_single (G : LabelledMultigraph) (e : G.Edge) :
    G.boundaryMap (Pi.single e 1) = G.boundary e := by
  classical
  ext v
  simp [boundaryMap, boundaryMatrix, Matrix.mulVec, Matrix.col_apply]

lemma boundaryMap_apply (G : LabelledMultigraph) (z : G.Edge → ZMod 2)
    (v : G.Vertex) :
    G.boundaryMap z v = ∑ e, G.boundary e v * z e := rfl

/-- Every boundary chain of a primal spanning-forest basis is generated by the
basis edges. -/
lemma boundary_mem_span_of_isBase {G : LabelledMultigraph} {B : Set G.Edge}
    (hB : (G.cycleMatroid).IsBase B) (e : G.Edge) :
    G.boundary e ∈ Submodule.span (ZMod 2) (G.boundary '' B) := by
  by_cases he : e ∈ B
  · exact Submodule.subset_span ⟨e, he, rfl⟩
  · apply G.boundary_mem_span_iff_reachable.mpr
    apply G.reachable_of_mem_diff_of_isBasis hB.isBasis_ground
    simpa using he

end FK.Finite.LabelledMultigraph


namespace FK.Finite.LabelledMultigraph

/-- The size of a cycle-matroid basis is the rank of the binary incidence
matrix. -/
theorem rank_boundaryMatrix_eq_ncard_of_isBase {G : LabelledMultigraph}
    {B : Set G.Edge} (hB : (G.cycleMatroid).IsBase B) :
    G.boundaryMatrix.rank = B.ncard := by
  classical
  have hli : LinearIndependent (ZMod 2) (fun e : B => G.boundary e) :=
    (G.cycleMatroid_indep_iff_linearIndepOn B).mp hB.indep
  have hc := (linearIndependent_iff_card_eq_finrank_span).mp hli
  have hrange : Set.range (fun e : B => G.boundary e) = G.boundary '' B := by
    ext y
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, e.property, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
  have hspan : Submodule.span (ZMod 2) (Set.range G.boundaryMatrix.col) =
      Submodule.span (ZMod 2) (G.boundary '' B) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨e, rfl⟩
      exact G.boundary_mem_span_of_isBase hB e
    · apply Submodule.span_mono
      rintro _ ⟨e, he, rfl⟩
      exact ⟨e, rfl⟩
  calc
    G.boundaryMatrix.rank =
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (Set.range G.boundaryMatrix.col)) :=
      Matrix.rank_eq_finrank_span_cols _
    _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (G.boundary '' B)) := congrArg
        (fun W : Submodule (ZMod 2) (G.Vertex → ZMod 2) =>
          Module.finrank (ZMod 2) W) hspan
    _ = Fintype.card B := by
      rw [← hrange]
      exact hc.symm
    _ = B.ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]

end FK.Finite.LabelledMultigraph

namespace FK.Finite.PlaneMatroid.LabelledDualPair

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional
open FK.FinitePlane

attribute [local instance] Classical.propDecidable

variable (P : LabelledDualPair)

/-- Faithful binary cellular input for a labelled dual pair.  The entries of
`faceBoundary` are the face-boundary chains.  `chain` and `exact` say precisely
`im ∂₂ ⊆ ker ∂₀` and `ker ∂₀ ⊆ im ∂₂`.  The last field identifies the transpose
of `∂₂` with the *actual* endpoint map of `P.faceDual`, stated pointwise by
`incidence`.

For a genuine finite polyhedral plane cell decomposition, exactness is the
vanishing of its first binary cellular homology.  No plane topology is proved
from the matrix alone, and no independence or matroid equality is assumed. -/
structure SphereChainData where
  faceBoundary : P.Face → P.Edge → ZMod 2
  chain : ∀ x : P.Face → ZMod 2,
    P.primal.boundaryMap (Matrix.mulVec (fun e f => faceBoundary f e) x) = 0
  exact : ∀ z : P.Edge → ZMod 2, P.primal.boundaryMap z = 0 →
    ∃ x : P.Face → ZMod 2, Matrix.mulVec (fun e f => faceBoundary f e) x = z
  incidence : ∀ (f : P.Face) (e : P.Edge),
    faceBoundary f e = P.faceDual.boundary e f

variable {P}

namespace SphereChainData

/-- The produced face-to-edge boundary map. -/
noncomputable def faceBoundaryMap (C : P.SphereChainData) :
    (P.Face → ZMod 2) →ₗ[ZMod 2] (P.Edge → ZMod 2) :=
  Matrix.mulVecLin (fun e f => C.faceBoundary f e)

lemma faceBoundaryMap_apply (C : P.SphereChainData) (x : P.Face → ZMod 2) :
    C.faceBoundaryMap x = Matrix.mulVec (fun e f => C.faceBoundary f e) x := rfl


lemma faceMatrix_transpose (C : P.SphereChainData) :
    (fun e f => C.faceBoundary f e) = Matrix.transpose P.faceDual.boundaryMatrix := by
  funext e f
  exact C.incidence f e

/-- The matrix transpose identity derived from pointwise face/dual incidence. -/
theorem dual_transpose (C : P.SphereChainData) (x : P.Face → ZMod 2)
    (z : P.Edge → ZMod 2) :
    dotProduct (Matrix.mulVec (fun e f => C.faceBoundary f e) x) z =
      dotProduct x (P.faceDual.boundaryMap z) := by
  rw [C.faceMatrix_transpose, dotProduct_comm]
  change dotProduct z (P.faceDual.boundaryMatrix.transpose.mulVec x) =
    dotProduct x (P.faceDual.boundaryMatrix.mulVec z)
  exact Matrix.dotProduct_transpose_mulVec P.faceDual.boundaryMatrix z x

/-- A dual cycle supported off a primal basis yields a primal 0-cochain. -/
lemma exists_primal_dualMap_of_dual_ker (C : P.SphereChainData)
    {z : P.primal.Edge → ZMod 2} (hz : P.faceDual.boundaryMap z = 0) :
    ∃ φ : Module.Dual (ZMod 2) (P.primal.Vertex → ZMod 2),
      P.primal.boundaryMap.dualMap φ = dotProductEquiv (ZMod 2) P.primal.Edge z := by
  classical
  have hann : dotProductEquiv (ZMod 2) P.primal.Edge z ∈
      (LinearMap.ker P.primal.boundaryMap).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    obtain ⟨x, rfl⟩ := C.exact y hy
    change dotProduct z (Matrix.mulVec (fun e f => C.faceBoundary f e) x) = 0
    rw [dotProduct_comm]
    calc
      _ = dotProduct x (P.faceDual.boundaryMap z) := C.dual_transpose x z
      _ = 0 := by
        rw [hz]
        change dotProduct x (0 : P.Face → ZMod 2) = 0
        exact dotProduct_zero x
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
  exact hann

/-- The crucial chain-complex geometric step.  A binary dual cycle which is
zero on every edge of a primal basis is identically zero: the dual-annihilator
identity turns it into a primal coboundary, and the basis spans every primal
edge boundary. -/
theorem dual_ker_eq_zero_of_isBase (C : P.SphereChainData) {B : Set P.primal.Edge}
    (hB : (P.primal.cycleMatroid).IsBase B) {z : P.primal.Edge → ZMod 2}
    (hz : P.faceDual.boundaryMap z = 0) (hzB : ∀ b ∈ B, z b = 0) : z = 0 := by
  classical
  obtain ⟨φ, hφ⟩ := C.exists_primal_dualMap_of_dual_ker hz
  have heval (e : P.primal.Edge) : z e = φ (P.primal.boundary e) := by
    have h := congrArg (fun L : Module.Dual (ZMod 2) (P.primal.Edge → ZMod 2) =>
      L (Pi.single e 1)) hφ
    change φ (P.primal.boundaryMap (Pi.single e 1)) =
      dotProduct z (Pi.single e 1) at h
    simpa using h.symm
  have hspan : Submodule.span (ZMod 2) (P.primal.boundary '' B) ≤
      LinearMap.ker φ := by
    apply Submodule.span_le.mpr
    rintro y ⟨b, hb, rfl⟩
    change φ (P.primal.boundary b) = 0
    rw [← heval, hzB b hb]
  funext e
  rw [heval]
  have he := P.primal.boundary_mem_span_of_isBase hB e
  have hzφ := hspan he
  exact hzφ

/-- A sum of face-dual boundary vectors gives a dual 1-chain with zero
boundary, with the unused coefficients explicitly zero. -/
lemma dual_boundaryMap_eq_zero_of_sum {C : P.SphereChainData}
    (t : Finset P.Edge) (g : P.Edge → ZMod 2)
    (hg : ∀ e ∉ t, g e = 0)
    (hsum : ∑ e ∈ t, g e • P.faceDual.boundary e = 0) :
    P.faceDual.boundaryMap g = 0 := by
  classical
  ext v
  change (∑ e, P.faceDual.boundary e v * g e) = 0
  have hv := congrFun hsum v
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hv
  calc
    (∑ e, P.faceDual.boundary e v * g e) =
        ∑ e ∈ t, P.faceDual.boundary e v * g e := by
      symm
      apply Finset.sum_subset (t.subset_univ)
      intro e _ het
      simp [hg e het]
    _ = ∑ e ∈ t, g e * P.faceDual.boundary e v := by
      apply Finset.sum_congr rfl
      intro e _
      exact mul_comm _ _
    _ = 0 := hv




/-- Pointwise transpose compatibility of face-boundary and face-dual endpoint
incidence. -/
lemma faceBoundary_entry (C : P.SphereChainData) (f : P.faceDual.Vertex)
    (e : P.faceDual.Edge) : C.faceBoundary f e = P.faceDual.boundary e f :=
  C.incidence f e

/-- One column of the face-boundary matrix as a chain on faces. -/
noncomputable def faceChain (C : P.SphereChainData) (e : P.faceDual.Edge) :
    P.faceDual.Vertex → ZMod 2 := fun f => C.faceBoundary f e

lemma faceChain_eq_dual_boundary (C : P.SphereChainData) (e : P.faceDual.Edge) :
    C.faceChain e = P.faceDual.boundary e := by
  funext f
  change C.faceBoundary f e = P.faceDual.boundary e f
  exact C.faceBoundary_entry f e

lemma faceBoundaryMap_single_pairing (C : P.SphereChainData)
    (x : P.faceDual.Vertex → ZMod 2) (e : P.faceDual.Edge) :
    dotProduct (C.faceBoundaryMap x) (Pi.single e 1) =
      dotProduct x (C.faceChain e) := by
  calc
    _ = dotProduct x (P.faceDual.boundaryMap (Pi.single e 1)) :=
      C.dual_transpose x (Pi.single e 1)
    _ = dotProduct x (C.faceChain e) := by
      rw [P.faceDual.boundaryMap_single, C.faceChain_eq_dual_boundary]

/-- Symmetric zero-cycle lemma.  A primal cycle supported off a face-dual
basis is zero: exactness writes it as a face boundary, and a dual-basis argument
shows that every coordinate vanishes. -/
theorem faceCoboundary_eq_zero_of_isBase (C : P.SphereChainData)
    {D : Set P.faceDual.Edge} (hD : (P.faceDual.cycleMatroid).IsBase D)
    {y : P.faceDual.Edge → ZMod 2} (hy : P.primal.boundaryMap y = 0)
    (hyD : ∀ d ∈ D, y d = 0) : y = 0 := by
  classical
  obtain ⟨x, hx⟩ := C.exact y hy
  let x' : P.faceDual.Vertex → ZMod 2 := x
  have heval (e : P.faceDual.Edge) : y e = dotProduct x' (C.faceChain e) := by
    calc
      y e = dotProduct y (Pi.single e 1) := (dotProduct_single_one y e).symm
      _ = dotProduct (C.faceBoundaryMap x') (Pi.single e 1) :=
        congrArg (fun z => dotProduct z (Pi.single e 1)) hx.symm
      _ = dotProduct x' (C.faceChain e) := C.faceBoundaryMap_single_pairing x' e
  have hspan : Submodule.span (ZMod 2) (C.faceChain '' D) ≤
      LinearMap.ker (pairingLinear x') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    change pairingLinear x' (C.faceChain d) = 0
    rw [pairingLinear_apply, ← heval d, hyD d hd]
  funext e
  have hmem : C.faceChain e ∈ Submodule.span (ZMod 2) (C.faceChain '' D) := by
    have hset : C.faceChain '' D = P.faceDual.boundary '' D := by
      ext y
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, (C.faceChain_eq_dual_boundary d).symm⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, hd, C.faceChain_eq_dual_boundary d⟩
    rw [C.faceChain_eq_dual_boundary, hset]
    exact P.faceDual.boundary_mem_span_of_isBase hD e
  have hz := hspan hmem
  have hz' : dotProduct x' (C.faceChain e) = 0 := by
    change pairingLinear x' (C.faceChain e) = 0 at hz
    rwa [pairingLinear_apply] at hz
  exact (heval e).trans hz'

/-- The complement of every primal spanning forest is independent in the actual
face-dual cycle matroid. -/
theorem faceDual_indep_compl_of_isBase (C : P.SphereChainData) {B : Set P.Edge}
    (hB : (P.primal.cycleMatroid).IsBase B) :
    (P.faceDual.cycleMatroid).Indep (Set.univ \ B) := by
  classical
  rw [P.faceDual.cycleMatroid_indep_iff_linearIndepOn, linearIndepOn_iff'']
  intro t g ht hg hsum i hit
  have hz := C.dual_boundaryMap_eq_zero_of_sum t g hg hsum
  have hgB : ∀ b ∈ B, g b = 0 := by
    intro b hb
    by_cases hbt : b ∈ t
    · have hbC := ht hbt
      exact (hbC.2 hb).elim
    · exact hg b hbt
  have hgzero := C.dual_ker_eq_zero_of_isBase hB hz hgB
  have hi := congrFun hgzero i
  exact hi



/-- Exactness at the edge module identifies the face-boundary range with the
primal cycle space.  The transpose incidence then gives the rank relation;
this is the numerical input which the one-sided basis lemmas do not provide. -/
theorem range_faceBoundaryMap_eq_ker_primal_boundaryMap (C : P.SphereChainData) :
    LinearMap.range C.faceBoundaryMap = LinearMap.ker P.primal.boundaryMap := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact C.chain x
  · intro z hz
    obtain ⟨x, hx⟩ := C.exact z hz
    exact ⟨x, hx⟩

theorem boundaryMatrix_rank_add_faceDual_rank (C : P.SphereChainData) :
    P.primal.boundaryMatrix.rank + P.faceDual.boundaryMatrix.rank =
      Fintype.card P.Edge := by
  have hp := P.primal.boundaryMap.finrank_range_add_finrank_ker
  rw [← C.range_faceBoundaryMap_eq_ker_primal_boundaryMap] at hp
  have hr : Module.finrank (ZMod 2) (LinearMap.range C.faceBoundaryMap) =
      P.faceDual.boundaryMatrix.rank := by
    change Matrix.rank (fun e f => C.faceBoundary f e) = P.faceDual.boundaryMatrix.rank
    rw [C.faceMatrix_transpose]
    exact Matrix.rank_transpose P.faceDual.boundaryMatrix
  simp only [Module.finrank_pi] at hp
  change P.primal.boundaryMatrix.rank +
    Module.finrank (ZMod 2) (LinearMap.range C.faceBoundaryMap) =
      Fintype.card P.Edge at hp
  rwa [hr] at hp

/-- Symmetric form of `faceDual_indep_compl_of_isBase`: the complement of a
face-dual spanning forest is independent in the primal cycle matroid. -/
theorem primal_indep_compl_of_isBase (C : P.SphereChainData)
    {D : Set P.Edge} (hD : (P.faceDual.cycleMatroid).IsBase D) :
    (P.primal.cycleMatroid).Indep (Set.univ \ D) := by
  classical
  rw [P.primal.cycleMatroid_indep_iff_linearIndepOn, linearIndepOn_iff'']
  intro t g ht hg hsum i hit
  have hy : P.primal.boundaryMap g = 0 := by
    ext v
    change (∑ e, P.primal.boundary e v * g e) = 0
    have hv := congrFun hsum v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hv
    calc
      (∑ e, P.primal.boundary e v * g e) =
          ∑ e ∈ t, P.primal.boundary e v * g e := by
        symm
        apply Finset.sum_subset (t.subset_univ)
        intro e _ het
        simp [hg e het]
      _ = ∑ e ∈ t, g e * P.primal.boundary e v := by
        apply Finset.sum_congr rfl
        intro e _
        exact mul_comm _ _
      _ = 0 := hv
  have hgD : ∀ d ∈ D, g d = 0 := by
    intro d hd
    by_cases hdt : d ∈ t
    · exact (ht hdt).2 hd |>.elim
    · exact hg d hdt
  exact congrFun (C.faceCoboundary_eq_zero_of_isBase hD hy hgD) i

/-- Exactness makes the complement of a primal spanning forest not merely
independent, but a base of the face-dual cycle matroid. -/
theorem faceDual_isBase_compl_of_isBase (C : P.SphereChainData)
    {B : Set P.Edge} (hB : (P.primal.cycleMatroid).IsBase B) :
    (P.faceDual.cycleMatroid).IsBase Bᶜ := by
  classical
  have hset : (Set.univ \ B : Set P.Edge) = Bᶜ := by ext; simp
  have hI : (P.faceDual.cycleMatroid).Indep Bᶜ := by
    have hI0 : (P.faceDual.cycleMatroid).Indep (Set.univ \ B : Set P.Edge) :=
      C.faceDual_indep_compl_of_isBase hB
    rwa [hset] at hI0
  obtain ⟨D, hD, hBD⟩ := hI.exists_isBase_superset
  change Set P.Edge at D
  have hr := C.boundaryMatrix_rank_add_faceDual_rank
  have hp : P.primal.boundaryMatrix.rank = (B : Set P.Edge).ncard :=
    P.primal.rank_boundaryMatrix_eq_ncard_of_isBase hB
  have hd : P.faceDual.boundaryMatrix.rank = (D : Set P.Edge).ncard :=
    P.faceDual.rank_boundaryMatrix_eq_ncard_of_isBase hD
  rw [hp, hd] at hr
  have hc : Bᶜ.ncard + B.ncard = Fintype.card P.Edge := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using
      Set.ncard_compl_add_ncard B
  have hcard : Bᶜ.ncard = D.ncard := by omega
  have heq : Bᶜ = D := Set.eq_of_subset_of_ncard_le hBD hcard.ge
  exact heq.symm ▸ hD

/-- The complementary-base statement in the other direction. -/
theorem primal_isBase_compl_of_isBase (C : P.SphereChainData)
    {D : Set P.Edge} (hD : (P.faceDual.cycleMatroid).IsBase D) :
    (P.primal.cycleMatroid).IsBase Dᶜ := by
  classical
  have hset : (Set.univ \ D : Set P.Edge) = Dᶜ := by ext; simp
  have hI : (P.primal.cycleMatroid).Indep Dᶜ := by
    have hI0 : (P.primal.cycleMatroid).Indep (Set.univ \ D : Set P.Edge) :=
      C.primal_indep_compl_of_isBase hD
    rwa [hset] at hI0
  obtain ⟨B, hB, hDB⟩ := hI.exists_isBase_superset
  change Set P.Edge at B
  have hr := C.boundaryMatrix_rank_add_faceDual_rank
  have hp : P.primal.boundaryMatrix.rank = (B : Set P.Edge).ncard :=
    P.primal.rank_boundaryMatrix_eq_ncard_of_isBase hB
  have hd : P.faceDual.boundaryMatrix.rank = (D : Set P.Edge).ncard :=
    P.faceDual.rank_boundaryMatrix_eq_ncard_of_isBase hD
  rw [hp, hd] at hr
  have hc : Dᶜ.ncard + D.ncard = Fintype.card P.Edge := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using
      Set.ncard_compl_add_ncard D
  have hcard : Dᶜ.ncard = B.ncard := by omega
  have heq : Dᶜ = B := Set.eq_of_subset_of_ncard_le hDB hcard.ge
  exact heq.symm ▸ hB

/-- Cellular binary exactness and the concrete transpose incidence imply the
actual labelled cycle-matroid duality.  No Euler, independence, rank, or
matroid-duality equality is assumed. -/
theorem cycleMatroid_dual_of_sphereChainData (C : P.SphereChainData) :
    (P.primal.cycleMatroid)✶ = P.faceDual.cycleMatroid := by
  apply Matroid.ext_isBase (by
    simp only [Matroid.dual_ground, LabelledMultigraph.cycleMatroid_ground]
    rfl)
  intro B hB
  rw [Matroid.dual_isBase_iff]
  have hset : P.primal.cycleMatroid.E \ B = Bᶜ := by
    ext
    simp [LabelledMultigraph.cycleMatroid_ground]
  rw [hset]
  constructor
  · intro hbase
    have hcomp := C.faceDual_isBase_compl_of_isBase hbase
    have hsets : (Bᶜ : Set P.Edge)ᶜ = B := by
      ext e
      change (¬ ¬ e ∈ B) ↔ e ∈ B
      simp
    exact hsets ▸ hcomp
  · intro hbase
    exact C.primal_isBase_compl_of_isBase hbase

end SphereChainData

/-- A cellular chain certificate supplies the Whitney equality in a graphic
certificate.  Nonempty facial vertices and their actual connectivity are kept
as separate geometric obligations. -/
theorem graphicDualCertificate_of_sphereChainData (P : LabelledDualPair)
    (C : P.SphereChainData) (hF : Nonempty P.Face)
    (hconn : (P.faceDual.connectionGraph P.faceDual.freeBoundary
      P.faceDual.allOpen).Preconnected) : P.GraphicDualCertificate where
  dual_cycleMatroid := C.cycleMatroid_dual_of_sphereChainData
  nonemptyFace := hF
  allOpen_preconnected := hconn

/-- The configurationwise component/Euler identity is a consequence of
cellular exactness, not an additional input. -/
theorem componentCount_dual_add_card_vertices_of_sphereChainData
    (P : LabelledDualPair) (C : P.SphereChainData) (hF : Nonempty P.Face)
    (hconn : (P.faceDual.connectionGraph P.faceDual.freeBoundary
      P.faceDual.allOpen).Preconnected) (ω : P.Edge → Bool) :
    P.faceDual.componentCount P.faceDual.freeBoundary
        (FK.Configuration.dualConfig (Equiv.refl P.Edge) ω) + Fintype.card P.Vertex =
      P.primal.componentCount P.primal.freeBoundary ω + 1 + openCard ω :=
  P.componentCount_dual_add_card_vertices
    (P.graphicDualCertificate_of_sphereChainData C hF hconn) ω

/-- Actual normalized FK duality from binary cellular exactness and the two
remaining finite facial-connectivity obligations. -/
theorem actual_fkPMF_duality_of_sphereChainData (P : LabelledDualPair)
    (C : P.SphereChainData) (hF : Nonempty P.Face)
    (hconn : (P.faceDual.connectionGraph P.faceDual.freeBoundary
      P.faceDual.allOpen).Preconnected)
    (q p : NNReal) (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (FK.Configuration.dualEquiv (Equiv.refl P.Edge))
        (P.primal.fkPMF hq hp₁.le P.primal.freeBoundary) =
      P.faceDual.fkPMF hq (dualParameter_le_one hq hp₁.le)
        P.faceDual.freeBoundary :=
  P.actual_fkPMF_graphicDual_duality
    (P.graphicDualCertificate_of_sphereChainData C hF hconn) q p hq hp₀ hp₁

end FK.Finite.PlaneMatroid.LabelledDualPair
