import FK.ThetaDuality
import Mathlib.Combinatorics.Matroid.Sum

open scoped BigOperators Classical
open Set

set_option backward.isDefEq.respectTransparency false

namespace FK.Finite.PlaneMatroid

/-- Duality commutes with the type-level direct sum of matroids. -/
theorem dual_sum {α β : Type*} (M : Matroid α) (N : Matroid β) :
    (M.sum N)✶ = M✶.sum N✶ := by
  apply Matroid.ext_isBase
  · simp [Matroid.sum_ground]
  · intro B hB
    constructor
    · intro h
      have hL := (Matroid.dual_isBase_iff').mp h
      have hsum := (Matroid.sum_isBase_iff).mp hL.1
      apply (Matroid.sum_isBase_iff).mpr
      constructor
      · apply (Matroid.dual_isBase_iff').mpr
        refine ⟨?_, ?_⟩
        · convert hsum.1 using 1 <;> ext x <;> simp
        · intro x hx
          have hx' := hL.2 hx
          simpa [Matroid.sum_ground] using hx'
      · apply (Matroid.dual_isBase_iff').mpr
        refine ⟨?_, ?_⟩
        · convert hsum.2 using 1 <;> ext x <;> simp
        · intro x hx
          have hx' := hL.2 hx
          simpa [Matroid.sum_ground] using hx'
    · intro h
      have hsum := (Matroid.sum_isBase_iff).mp h
      apply (Matroid.dual_isBase_iff').mpr
      refine ⟨(Matroid.sum_isBase_iff).mpr ⟨?_, ?_⟩, ?_⟩
      · convert (Matroid.dual_isBase_iff').mp hsum.1 |>.1 using 1 <;> ext x <;> simp
      · convert (Matroid.dual_isBase_iff').mp hsum.2 |>.1 using 1 <;> ext x <;> simp
      · rw [Matroid.sum_ground]
        intro x hx
        rcases x with x | x
        · exact Or.inl ⟨x, hsum.1.subset_ground hx, rfl⟩
        · exact Or.inr ⟨x, hsum.2.subset_ground hx, rfl⟩

end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid

open FK.Finite FK.Finite.LabelledMultigraph

/-- Vertices of a one-point union: `a` is removed from the left copy and
represented by the base point in the right copy. -/
abbrev VertexGlue (α β : Type*) (a : α) := {x : α // x ≠ a} ⊕ β

noncomputable instance {α β : Type*} [Fintype α] [Fintype β] (a : α) :
    Fintype (VertexGlue α β a) := by
  classical
  unfold VertexGlue
  infer_instance

/-- The injection of the left vertex set into a one-point union. -/
noncomputable def glueLeft {α β : Type*} (a : α) (b : β) (x : α) :
    VertexGlue α β a :=
  if h : x = a then Sum.inr b else Sum.inl ⟨x, h⟩

/-- The injection of the right vertex set into a one-point union. -/
def glueRight {α β : Type*} (a : α) (x : β) : VertexGlue α β a := Sum.inr x

/-- Retract a one-point union to its left factor, collapsing the right factor
to the glued vertex. -/
def unglueLeft {α β : Type*} {a : α} : VertexGlue α β a → α
  | Sum.inl x => x.1
  | Sum.inr _ => a

/-- Retract a one-point union to its right factor, collapsing the left factor
to the glued vertex. -/
def unglueRight {α β : Type*} {a : α} (b : β) : VertexGlue α β a → β
  | Sum.inl _ => b
  | Sum.inr x => x

@[simp] lemma unglueLeft_glueLeft {α β : Type*} (a : α) (b : β) (x : α) :
    unglueLeft (glueLeft a b x) = x := by
  classical
  by_cases h : x = a <;> simp [glueLeft, unglueLeft, h]

@[simp] lemma unglueLeft_glueRight {α β : Type*} (a : α) (x : β) :
    unglueLeft (glueRight a x) = a := rfl

@[simp] lemma unglueRight_glueLeft {α β : Type*} (a : α) (b : β) (x : α) :
    unglueRight b (glueLeft a b x) = b := by
  classical
  by_cases h : x = a <;> simp [glueLeft, unglueRight, h]

@[simp] lemma unglueRight_glueRight {α β : Type*} (a : α) (b : β) (x : β) :
    unglueRight b (glueRight a x) = x := rfl

lemma glueLeft_injective {α β : Type*} (a : α) (b : β) :
    Function.Injective (glueLeft a b) := by
  intro x y h
  have h' := congrArg unglueLeft h
  simpa using h'

lemma glueRight_injective {α β : Type*} (a : α) :
    Function.Injective (glueRight (β := β) a) := by
  intro x y h
  injection h

/-- One-point union of labelled multigraphs, retaining both edge-label types
as a disjoint sum. -/
noncomputable abbrev wedgeGraph (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) : LabelledMultigraph where
  Vertex := VertexGlue G.Vertex H.Vertex v
  Edge := G.Edge ⊕ H.Edge
  source
    | Sum.inl e => glueLeft v w (G.source e)
    | Sum.inr e => glueRight v (H.source e)
  target
    | Sum.inl e => glueLeft v w (G.target e)
    | Sum.inr e => glueRight v (H.target e)

/-- The left inclusion is a graph homomorphism for every wedge configuration
with the prescribed left restriction. -/
noncomputable def wedgeLeftHom (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) (ω : G.Configuration)
    (ρ : (wedgeGraph G H v w).Configuration)
    (hω : ∀ e, ρ (Sum.inl e) = ω e) :
    G.connectionGraph G.freeBoundary ω →g
      (wedgeGraph G H v w).connectionGraph (wedgeGraph G H v w).freeBoundary ρ where
  toFun := glueLeft v w
  map_rel' := by
    intro x y hxy
    refine ⟨(glueLeft_injective v w).ne hxy.1, ?_⟩
    rcases hxy.2 with hfree | ⟨e, he, hjoin⟩
    · exact (hxy.1 hfree).elim
    · refine Or.inr ⟨Sum.inl e, (hω e).trans he, ?_⟩
      rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨congrArg (glueLeft v w) hs, congrArg (glueLeft v w) ht⟩
      · exact Or.inr ⟨congrArg (glueLeft v w) hs, congrArg (glueLeft v w) ht⟩

/-- The right inclusion is a graph homomorphism for every wedge configuration
with the prescribed right restriction. -/
noncomputable def wedgeRightHom (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) (η : H.Configuration)
    (ρ : (wedgeGraph G H v w).Configuration)
    (hη : ∀ e, ρ (Sum.inr e) = η e) :
    H.connectionGraph H.freeBoundary η →g
      (wedgeGraph G H v w).connectionGraph (wedgeGraph G H v w).freeBoundary ρ where
  toFun := glueRight v
  map_rel' := by
    intro x y hxy
    refine ⟨(glueRight_injective v).ne hxy.1, ?_⟩
    rcases hxy.2 with hfree | ⟨e, he, hjoin⟩
    · exact (hxy.1 hfree).elim
    · refine Or.inr ⟨Sum.inr e, (hη e).trans he, ?_⟩
      rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨congrArg (glueRight v) hs, congrArg (glueRight v) ht⟩
      · exact Or.inr ⟨congrArg (glueRight v) hs, congrArg (glueRight v) ht⟩

end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid

open FK.Finite FK.Finite.LabelledMultigraph

/-- One wedge adjacency projects to left reachability.  A right edge is
collapsed to a reflexive step at the glued vertex. -/
lemma reachable_unglueLeft_of_adj (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) (ω : G.Configuration)
    (ρ : (wedgeGraph G H v w).Configuration)
    (hω : ∀ e, ρ (Sum.inl e) = ω e)
    {x y : (wedgeGraph G H v w).Vertex}
    (hxy : ((wedgeGraph G H v w).connectionGraph
      (wedgeGraph G H v w).freeBoundary ρ).Adj x y) :
    (G.connectionGraph G.freeBoundary ω).Reachable (unglueLeft x) (unglueLeft y) := by
  rcases hxy.2 with hfree | ⟨e, he, hjoin⟩
  · exact (hxy.1 hfree).elim
  · cases e with
    | inl e =>
      apply SimpleGraph.Adj.reachable
      have hproj : G.Joins e (unglueLeft x) (unglueLeft y) := by
        rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · apply Or.inl
          constructor
          · have h := congrArg unglueLeft hs
            simpa [wedgeGraph] using h
          · have h := congrArg unglueLeft ht
            simpa [wedgeGraph] using h
        · apply Or.inr
          constructor
          · have h := congrArg unglueLeft hs
            simpa [wedgeGraph] using h
          · have h := congrArg unglueLeft ht
            simpa [wedgeGraph] using h
      refine ⟨?_, Or.inr ⟨e, (hω e).symm.trans he, hproj⟩⟩
      intro hp
      apply hxy.1
      rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · have hsx : G.source e = unglueLeft x := by
          have h := congrArg unglueLeft hs
          simpa [wedgeGraph] using h
        have hty : G.target e = unglueLeft y := by
          have h := congrArg unglueLeft ht
          simpa [wedgeGraph] using h
        have hst : G.source e = G.target e := hsx.trans (hp.trans hty.symm)
        change glueLeft v w (G.source e) = x at hs
        change glueLeft v w (G.target e) = y at ht
        exact hs.symm.trans ((congrArg (glueLeft v w) hst).trans ht)
      · have hsy : G.source e = unglueLeft y := by
          have h := congrArg unglueLeft hs
          simpa [wedgeGraph] using h
        have htx : G.target e = unglueLeft x := by
          have h := congrArg unglueLeft ht
          simpa [wedgeGraph] using h
        have hst : G.source e = G.target e := hsy.trans (hp.symm.trans htx.symm)
        change glueLeft v w (G.source e) = y at hs
        change glueLeft v w (G.target e) = x at ht
        exact ht.symm.trans ((congrArg (glueLeft v w) hst.symm).trans hs)
    | inr e =>
      have hp : unglueLeft x = unglueLeft y := by
        rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · rw [← hs, ← ht]
          simp [wedgeGraph]
        · rw [← hs, ← ht]
          simp [wedgeGraph]
      exact hp ▸ SimpleGraph.Reachable.refl _

/-- Walks in a one-point union project to walks in the left factor. -/
lemma reachable_unglueLeft (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) (ω : G.Configuration)
    (ρ : (wedgeGraph G H v w).Configuration)
    (hω : ∀ e, ρ (Sum.inl e) = ω e)
    {x y : (wedgeGraph G H v w).Vertex}
    (h : ((wedgeGraph G H v w).connectionGraph
      (wedgeGraph G H v w).freeBoundary ρ).Reachable x y) :
    (G.connectionGraph G.freeBoundary ω).Reachable (unglueLeft x) (unglueLeft y) := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih => exact (reachable_unglueLeft_of_adj G H v w ω ρ hω h).trans ih

end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid

open FK.Finite FK.Finite.LabelledMultigraph

/-- One wedge adjacency projects to right reachability. -/
lemma reachable_unglueRight_of_adj (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) (η : H.Configuration)
    (ρ : (wedgeGraph G H v w).Configuration)
    (hη : ∀ e, ρ (Sum.inr e) = η e)
    {x y : (wedgeGraph G H v w).Vertex}
    (hxy : ((wedgeGraph G H v w).connectionGraph
      (wedgeGraph G H v w).freeBoundary ρ).Adj x y) :
    (H.connectionGraph H.freeBoundary η).Reachable
      (unglueRight w x) (unglueRight w y) := by
  rcases hxy.2 with hfree | ⟨e, he, hjoin⟩
  · exact (hxy.1 hfree).elim
  · cases e with
    | inl e =>
      have hp : unglueRight w x = unglueRight w y := by
        rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · rw [← hs, ← ht]
          simp [wedgeGraph]
        · rw [← hs, ← ht]
          simp [wedgeGraph]
      exact hp ▸ SimpleGraph.Reachable.refl _
    | inr e =>
      apply SimpleGraph.Adj.reachable
      have hproj : H.Joins e (unglueRight w x) (unglueRight w y) := by
        rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · apply Or.inl
          constructor
          · have h := congrArg (unglueRight w) hs
            simpa [wedgeGraph] using h
          · have h := congrArg (unglueRight w) ht
            simpa [wedgeGraph] using h
        · apply Or.inr
          constructor
          · have h := congrArg (unglueRight w) hs
            simpa [wedgeGraph] using h
          · have h := congrArg (unglueRight w) ht
            simpa [wedgeGraph] using h
      refine ⟨?_, Or.inr ⟨e, (hη e).symm.trans he, hproj⟩⟩
      intro hp
      apply hxy.1
      rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · have hsx : H.source e = unglueRight w x := by
          have h := congrArg (unglueRight w) hs
          simpa [wedgeGraph] using h
        have hty : H.target e = unglueRight w y := by
          have h := congrArg (unglueRight w) ht
          simpa [wedgeGraph] using h
        have hst : H.source e = H.target e := hsx.trans (hp.trans hty.symm)
        change glueRight v (H.source e) = x at hs
        change glueRight v (H.target e) = y at ht
        exact hs.symm.trans ((congrArg (glueRight v) hst).trans ht)
      · have hsy : H.source e = unglueRight w y := by
          have h := congrArg (unglueRight w) hs
          simpa [wedgeGraph] using h
        have htx : H.target e = unglueRight w x := by
          have h := congrArg (unglueRight w) ht
          simpa [wedgeGraph] using h
        have hst : H.source e = H.target e := hsy.trans (hp.symm.trans htx.symm)
        change glueRight v (H.source e) = y at hs
        change glueRight v (H.target e) = x at ht
        exact ht.symm.trans ((congrArg (glueRight v) hst.symm).trans hs)

/-- Walks in a one-point union project to walks in the right factor. -/
lemma reachable_unglueRight (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) (η : H.Configuration)
    (ρ : (wedgeGraph G H v w).Configuration)
    (hη : ∀ e, ρ (Sum.inr e) = η e)
    {x y : (wedgeGraph G H v w).Vertex}
    (h : ((wedgeGraph G H v w).connectionGraph
      (wedgeGraph G H v w).freeBoundary ρ).Reachable x y) :
    (H.connectionGraph H.freeBoundary η).Reachable
      (unglueRight w x) (unglueRight w y) := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih => exact (reachable_unglueRight_of_adj G H v w η ρ hη h).trans ih

end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid

open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional FK.FinitePlane
open FK.FiniteFiber

/-- Forests in a one-point union are exactly pairs of forests in the factors.
In particular, no walk can use the other factor to close a cycle. -/
lemma isOpenForest_wedge_iff (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) (ω : G.Configuration) (η : H.Configuration) :
    (wedgeGraph G H v w).IsOpenForest (wedgeGraph G H v w).freeBoundary
        (Sum.elim ω η) ↔
      G.IsOpenForest G.freeBoundary ω ∧ H.IsOpenForest H.freeBoundary η := by
  letI : DecidableEq (wedgeGraph G H v w).Edge := Classical.decEq _
  constructor
  · intro h
    constructor
    · intro e he hconn
      apply h (Sum.inl e) he
      unfold endpointsConnectedWithout at hconn ⊢
      exact hconn.map (wedgeLeftHom G H v w (withEdge e false ω)
        (withEdge (Sum.inl e) false (Sum.elim ω η)) (by
          intro a
          by_cases ha : a = e <;> simp [withEdge, ha]))
    · intro e he hconn
      apply h (Sum.inr e) he
      unfold endpointsConnectedWithout at hconn ⊢
      exact hconn.map (wedgeRightHom G H v w (withEdge e false η)
        (withEdge (Sum.inr e) false (Sum.elim ω η)) (by
          intro a
          by_cases ha : a = e <;> simp [withEdge, ha]))
  · rintro ⟨hG, hH⟩ e he hconn
    cases e with
    | inl e =>
      apply hG e he
      unfold endpointsConnectedWithout at hconn ⊢
      have hp := reachable_unglueLeft G H v w (withEdge e false ω)
        (withEdge (Sum.inl e) false (Sum.elim ω η)) (by
          intro a
          by_cases ha : a = e <;> simp [withEdge, ha]) hconn
      simpa using hp
    | inr e =>
      apply hH e he
      unfold endpointsConnectedWithout at hconn ⊢
      have hp := reachable_unglueRight G H v w (withEdge e false η)
        (withEdge (Sum.inr e) false (Sum.elim ω η)) (by
          intro a
          by_cases ha : a = e <;> simp [withEdge, ha]) hconn
      simpa using hp

/-- The labelled cycle matroid of a one-point union is the matroid direct sum. -/
theorem cycleMatroid_wedge (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex) :
    (wedgeGraph G H v w).cycleMatroid = G.cycleMatroid.sum H.cycleMatroid := by
  apply Matroid.ext_indep
  · ext e
    cases e <;> simp [Matroid.sum_ground] <;> rfl
  · intro A hA
    let ω := G.setConfig (Sum.inl ⁻¹' A)
    let η := H.setConfig (Sum.inr ⁻¹' A)
    have hcfg : (wedgeGraph G H v w).setConfig A = Sum.elim ω η := by
      funext e
      cases e <;> simp [wedgeGraph, setConfig, ω, η] <;> rfl
    rw [Matroid.sum_indep_iff]
    change (wedgeGraph G H v w).IsOpenForest _ ((wedgeGraph G H v w).setConfig A) ↔
      G.IsOpenForest G.freeBoundary (G.setConfig (Sum.inl ⁻¹' A)) ∧
        H.IsOpenForest H.freeBoundary (H.setConfig (Sum.inr ⁻¹' A))
    rw [hcfg, isOpenForest_wedge_iff]

end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid

open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional FK.FinitePlane
open FK.FiniteFiber

@[simp] lemma glueLeft_self {α β : Type*} (a : α) (b : β) :
    glueLeft a b a = glueRight a b := by
  classical
  simp [glueLeft, glueRight]

/-- The all-open graph of a wedge is preconnected when both factors are. -/
lemma preconnected_wedge_allOpen (G H : LabelledMultigraph)
    (v : G.Vertex) (w : H.Vertex)
    (hG : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (hH : (H.connectionGraph H.freeBoundary H.allOpen).Preconnected) :
    ((wedgeGraph G H v w).connectionGraph (wedgeGraph G H v w).freeBoundary
      (wedgeGraph G H v w).allOpen).Preconnected := by
  have hub : ∀ z, ((wedgeGraph G H v w).connectionGraph
      (wedgeGraph G H v w).freeBoundary (wedgeGraph G H v w).allOpen).Reachable
        z (glueRight v w) := by
    intro z
    cases z with
    | inl z =>
      have h := (hG z.1 v).map (wedgeLeftHom G H v w G.allOpen
        (wedgeGraph G H v w).allOpen (fun _ => rfl))
      change ((wedgeGraph G H v w).connectionGraph (wedgeGraph G H v w).freeBoundary
        (wedgeGraph G H v w).allOpen).Reachable
          (glueLeft v w z.1) (glueLeft v w v) at h
      simpa [glueLeft, glueRight, z.2] using h
    | inr z =>
      have h := (hH z w).map (wedgeRightHom G H v w H.allOpen
        (wedgeGraph G H v w).allOpen (fun _ => rfl))
      change ((wedgeGraph G H v w).connectionGraph (wedgeGraph G H v w).freeBoundary
        (wedgeGraph G H v w).allOpen).Reachable
          (glueRight v z) (glueRight v w) at h
      exact h
  intro x y
  exact (hub x).trans (hub y).symm

/-- Simultaneous one-point unions of a graphic pair at primal vertices and at
selected exterior faces. -/
noncomputable abbrev wedgePair (P Q : LabelledDualPair)
    (v : P.Vertex) (w : Q.Vertex) (f : P.Face) (g : Q.Face) : LabelledDualPair where
  Vertex := VertexGlue P.Vertex Q.Vertex v
  Face := VertexGlue P.Face Q.Face f
  Edge := P.Edge ⊕ Q.Edge
  fintypeVertex := (wedgeGraph P.primal Q.primal v w).fintypeVertex
  fintypeFace := (wedgeGraph P.faceDual Q.faceDual f g).fintypeVertex
  fintypeEdge := (wedgeGraph P.primal Q.primal v w).fintypeEdge
  source := (wedgeGraph P.primal Q.primal v w).source
  target := (wedgeGraph P.primal Q.primal v w).target
  dualSource := (wedgeGraph P.faceDual Q.faceDual f g).source
  dualTarget := (wedgeGraph P.faceDual Q.faceDual f g).target

@[simp] lemma wedgePair_primal (P Q : LabelledDualPair)
    (v : P.Vertex) (w : Q.Vertex) (f : P.Face) (g : Q.Face) :
    (wedgePair P Q v w f g).primal = wedgeGraph P.primal Q.primal v w := by
  rfl

@[simp] lemma wedgePair_faceDual (P Q : LabelledDualPair)
    (v : P.Vertex) (w : Q.Vertex) (f : P.Face) (g : Q.Face) :
    (wedgePair P Q v w f g).faceDual = wedgeGraph P.faceDual Q.faceDual f g := by
  rfl

/-- Graphic matroid duality is preserved by planar one-point unions.  The two
selected faces are the exterior faces merged by the geometric operation. -/
theorem graphicDualCertificate_wedge (P Q : LabelledDualPair)
    (v : P.Vertex) (w : Q.Vertex) (f : P.Face) (g : Q.Face)
    (hP : P.GraphicDualCertificate) (hQ : Q.GraphicDualCertificate) :
    (wedgePair P Q v w f g).GraphicDualCertificate := by
  refine ⟨?_, ⟨glueRight f g⟩, ?_⟩
  · change ((wedgeGraph P.primal Q.primal v w).cycleMatroid)✶ =
      (wedgeGraph P.faceDual Q.faceDual f g).cycleMatroid
    rw [cycleMatroid_wedge, cycleMatroid_wedge, dual_sum,
      hP.dual_cycleMatroid, hQ.dual_cycleMatroid]
  · exact preconnected_wedge_allOpen P.faceDual Q.faceDual f g
      hP.allOpen_preconnected hQ.allOpen_preconnected

end FK.Finite.PlaneMatroid


namespace FK.Finite.PlaneMatroid

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane

universe u v w

/-- A certified block together with the two points used in a wedge.  The
certificate is data supplied by the block construction, not a global planar
duality assumption.  In a geometric application `exteriorFace` is the face
placed on the common exterior by the chosen embedding. -/
structure PointedCertifiedPair where
  pair : LabelledDualPair.{u, v, w}
  attachment : pair.Vertex
  exteriorFace : pair.Face
  certificate : pair.GraphicDualCertificate

/-- Wedge two certified blocks, retaining the right attachment vertex and the
new common exterior face as the canonical points for a subsequent wedge. -/
noncomputable def pointedWedge (P Q : PointedCertifiedPair.{u, v, w}) :
    PointedCertifiedPair.{u, v, w} where
  pair := wedgePair P.pair Q.pair P.attachment Q.attachment P.exteriorFace Q.exteriorFace
  attachment := glueRight P.attachment Q.attachment
  exteriorFace := glueRight P.exteriorFace Q.exteriorFace
  certificate := graphicDualCertificate_wedge P.pair Q.pair P.attachment Q.attachment
    P.exteriorFace Q.exteriorFace P.certificate Q.certificate

/-- Assemble a finite chain of pointed blocks.  The `n`th new block is wedged
to the right attachment vertex of the preceding chain, and its selected face
is merged with the preceding common exterior face. -/
noncomputable def assemblePointed (P : PointedCertifiedPair.{u, v, w}) :
    List PointedCertifiedPair.{u, v, w} → PointedCertifiedPair.{u, v, w}
  | [] => P
  | Q :: Qs => assemblePointed (pointedWedge P Q) Qs

@[simp] lemma assemblePointed_nil (P : PointedCertifiedPair.{u, v, w}) :
    assemblePointed P [] = P := rfl

@[simp] lemma assemblePointed_cons (P Q : PointedCertifiedPair.{u, v, w})
    (Qs : List PointedCertifiedPair.{u, v, w}) :
    assemblePointed P (Q :: Qs) = assemblePointed (pointedWedge P Q) Qs := rfl

/-- Every finite pointed chain has an exact graphic dual certificate. -/
theorem graphicDualCertificate_assemblePointed
    (P : PointedCertifiedPair.{u, v, w}) (Ps : List PointedCertifiedPair.{u, v, w}) :
    (assemblePointed P Ps).pair.GraphicDualCertificate :=
  (assemblePointed P Ps).certificate

/-- Removing the identified left copy of a vertex leaves one fewer point. -/
lemma card_vertexGlue_add_one {α β : Type*} [Fintype α] [Fintype β] (a : α) :
    Fintype.card (VertexGlue α β a) + 1 = Fintype.card α + Fintype.card β := by
  classical
  have ha : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  simp only [VertexGlue, Fintype.card_sum]
  rw [show Fintype.card {x : α // x ≠ a} = Fintype.card α - 1 by
    simpa using Fintype.card_subtype_compl (fun x : α => x = a)]
  omega

/-- A primal/dual wedge identifies one pair of face vertices; all other face
vertices are retained. -/
lemma card_faces_pointedWedge (P Q : PointedCertifiedPair.{u, v, w}) :
    Fintype.card (pointedWedge P Q).pair.Face + 1 =
      Fintype.card P.pair.Face + Fintype.card Q.pair.Face := by
  exact card_vertexGlue_add_one P.exteriorFace

/-- Fold-level exterior-face accounting: every added block contributes its
face count, while the additive correction is exactly one per identification. -/
lemma card_faces_assemblePointed (P : PointedCertifiedPair.{u, v, w})
    (Ps : List PointedCertifiedPair.{u, v, w}) :
    Fintype.card (assemblePointed P Ps).pair.Face + Ps.length =
      Fintype.card P.pair.Face + (Ps.map fun Q => Fintype.card Q.pair.Face).sum := by
  induction Ps generalizing P with
  | nil => simp
  | cons Q Qs ih =>
      rw [assemblePointed_cons]
      have h := ih (pointedWedge P Q)
      have hcard := card_faces_pointedWedge P Q
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- A connected labelled cycle with a chosen attachment vertex and a chosen
one of its two faces. -/
structure CycleBlock where
  graph : LabelledMultigraph.{u, w}
  isCycle : graph.IsLabelledCycle
  attachment : graph.Vertex
  exteriorFace : Bool

/-- The exact two-face dual certificate already constructed for a labelled
cycle, equipped with its wedge data. -/
noncomputable def CycleBlock.toPointed (B : CycleBlock.{u, w}) :
    PointedCertifiedPair.{u, 0, w} where
  pair := LabelledDualPair.cyclePair B.graph
  attachment := B.attachment
  exteriorFace := B.exteriorFace
  certificate := LabelledDualPair.graphicDualCertificate_cycle B.graph B.isCycle

@[simp] lemma card_faces_cycleBlock_toPointed (B : CycleBlock.{u, w}) :
    Fintype.card B.toPointed.pair.Face = 2 := by
  change Fintype.card Bool = 2
  norm_num

/-- The explicit plane-dual pair of a nonempty chain of connected labelled
cycles.  Loops, digons and longer cycles may all occur as blocks. -/
noncomputable def cycleChainPair (B : CycleBlock.{u, w}) (Bs : List CycleBlock.{u, w}) :
    LabelledDualPair.{u, 0, w} :=
  (assemblePointed B.toPointed (Bs.map fun C => C.toPointed)).pair

/-- A chain with `Bs.length + 1` cycle blocks has exactly `Bs.length + 2`
face vertices: each new cycle brings two faces and the exterior merge removes
one. -/
lemma card_faces_cycleChainPair (B : CycleBlock.{u, w}) (Bs : List CycleBlock.{u, w}) :
    Fintype.card (cycleChainPair B Bs).Face = Bs.length + 2 := by
  have h := card_faces_assemblePointed B.toPointed (Bs.map fun C => C.toPointed)
  simp [List.map_map, Function.comp_def] at h
  unfold cycleChainPair
  omega

/-- Exact graphic matroid duality for every finite nonempty vertex-link chain
of connected labelled cycles, with arbitrary labelled edge types. -/
theorem graphicDualCertificate_cycleChain (B : CycleBlock.{u, w})
    (Bs : List CycleBlock.{u, w}) : (cycleChainPair B Bs).GraphicDualCertificate := by
  unfold cycleChainPair
  exact graphicDualCertificate_assemblePointed B.toPointed (Bs.map fun C => C.toPointed)

end FK.Finite.PlaneMatroid
