import FK.PlanarMatroid
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Cellular sphere duality for labelled multigraphs

This file derives graphic matroid duality from a two-dimensional cell complex,
not from an independent-set hypothesis. The field is `ZMod 2`, so unoriented
incidence retains loops and parallel labelled edges.
-/

namespace FK.Finite.PlaneMatroid

open scoped BigOperators Classical
open FK.Finite.LabelledMultigraph
open FK.FinitePlane
open FK.Finite.Conditional
open FK.FiniteFiber

namespace Cellular

abbrev F2 := ZMod 2

/-- The unoriented incidence matrix of a labelled multigraph. A loop has zero
column over `F2`, as it must for the graphic representation. -/
noncomputable def incidence (G : LabelledMultigraph) : Matrix G.Vertex G.Edge F2 :=
  fun v e => (if v = G.source e then 1 else 0) +
    (if v = G.target e then 1 else 0)

/-- The graph boundary map from edge chains to vertex chains. -/
noncomputable def boundary (G : LabelledMultigraph) :
    (G.Edge → F2) →ₗ[F2] (G.Vertex → F2) :=
  (incidence G).mulVecLin

/-- The graph coboundary map, sending a vertex potential to its edge cuts. -/
noncomputable def coboundary (G : LabelledMultigraph) :
    (G.Vertex → F2) →ₗ[F2] (G.Edge → F2) :=
  (incidence G).transpose.mulVecLin

lemma boundary_apply (G : LabelledMultigraph) (x : G.Edge → F2)
    (v : G.Vertex) :
    boundary G x v = ∑ e, ((if v = G.source e then x e else 0) +
      (if v = G.target e then x e else 0)) := by
  classical
  rw [boundary, Matrix.mulVecLin_apply]
  change (∑ e, ((if v = G.source e then (1 : F2) else 0) +
    (if v = G.target e then 1 else 0)) * x e) = _
  simp_rw [add_mul, ite_mul, one_mul, zero_mul]

lemma coboundary_apply (G : LabelledMultigraph) (p : G.Vertex → F2)
    (e : G.Edge) :
    coboundary G p e = p (G.source e) + p (G.target e) := by
  classical
  rw [coboundary, Matrix.mulVecLin_apply]
  change (∑ v, ((if v = G.source e then (1 : F2) else 0) +
    (if v = G.target e then 1 else 0)) * p v) = _
  simp_rw [add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp

lemma boundary_eq_zero_iff (G : LabelledMultigraph) (x : G.Edge → F2) :
    boundary G x = 0 ↔ ∀ v, (∑ e, ((if v = G.source e then x e else 0) +
      (if v = G.target e then x e else 0))) = 0 := by
  rw [funext_iff]
  simp only [Pi.zero_apply]
  exact forall_congr' fun v => by rw [boundary_apply G]

lemma coboundary_eq_zero_of_preconnected (G : LabelledMultigraph)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (p : G.Vertex → F2) (hp : coboundary G p = 0) (u v : G.Vertex) :
    p u = p v := by
  have hadj : ∀ {u v : G.Vertex},
      (G.connectionGraph G.freeBoundary G.allOpen).Adj u v → p u = p v := by
    intro u v huv
    rcases huv.2 with hfree | ⟨e, he, hjoin⟩
    · exact (huv.1 hfree).elim
    · have hz : p (G.source e) + p (G.target e) = 0 := by
        rw [← coboundary_apply G, hp]
        rfl
      have hadd (a b : F2) (hab : a + b = 0) : a = b := by
        rw [add_eq_zero_iff_eq_neg] at hab
        simpa using hab
      rcases hjoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadd _ _ hz
      · exact (hadd _ _ hz).symm
  obtain ⟨w⟩ := hconn u v
  induction w with
  | nil => rfl
  | cons h w ih => exact (hadj h).trans ih


/-- A set of edges is linearly independent when no nonzero chain supported on
it has zero boundary. This formulation does not need a subtype of the set. -/
def F2Independent (G : LabelledMultigraph) (A : Set G.Edge) : Prop :=
  ∀ x : G.Edge → F2, (∀ e, x e ≠ 0 → e ∈ A) → boundary G x = 0 → x = 0

lemma boundary_single (G : LabelledMultigraph) (e : G.Edge) :
    boundary G (Pi.single e 1) =
      Pi.single (G.source e) (1 : F2) + Pi.single (G.target e) (1 : F2) := by
  classical
  rw [boundary, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  funext v
  simp [incidence, Pi.single_apply]

/-- Adjacency of the unoriented incidence and coboundary maps. -/
lemma dot_coboundary_boundary (G : LabelledMultigraph) (p : G.Vertex → F2)
    (x : G.Edge → F2) :
    (∑ e, coboundary G p e * x e) = ∑ v, p v * boundary G x v := by
  classical
  have h := Matrix.dotProduct_mulVec p (incidence G) x
  have ht : Matrix.vecMul p (incidence G) = Matrix.mulVec (incidence G).transpose p := by
    simpa using Matrix.vecMul_transpose (incidence G).transpose p
  rw [ht] at h
  simpa only [dotProduct, coboundary, boundary, Matrix.mulVecLin_apply] using h.symm

lemma f2_add_add_cancel_middle (a b c : F2) : (a + b) + (b + c) = a + c := by
  calc
    _ = a + (b + b) + c := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

lemma f2_add_add_cancel_left (a b c : F2) : (a + b) + (c + a) = b + c := by
  calc
    _ = b + (a + a) + c := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

lemma f2_add_add_cancel_first (a b c : F2) : (a + b) + (a + c) = b + c := by
  calc
    _ = b + (a + a) + c := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

lemma f2_add_self_twice (a b : F2) : (a + b) + (a + b) = 0 := by
  calc
    _ = (a + a) + (b + b) := by ac_rfl
    _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

/-- A labelled walk gives a chain supported on its labelled edges, whose
boundary is the sum of its endpoints. No simplicity or edge injectivity is
needed: repeated and parallel labels are accumulated modulo two. -/
lemma exists_chain_boundary_of_walk (G : LabelledMultigraph)
    (ω : G.Configuration) {u v : G.Vertex}
    (w : (G.connectionGraph G.freeBoundary ω).Walk u v) :
    ∃ x : G.Edge → F2, (∀ e, x e ≠ 0 → ω e = true) ∧
      boundary G x = Pi.single u (1 : F2) + Pi.single v (1 : F2) := by
  classical
  induction w with
  | nil =>
      refine ⟨0, ?_, ?_⟩
      · intro e he
        simp at he
      · rw [map_zero]
        funext t
        exact (CharTwo.add_self_eq_zero _).symm
  | @cons u v z hvw path ih =>
      rcases ih with ⟨x, hx, hbx⟩
      rcases hvw.2 with hfree | ⟨e, he, hjoin⟩
      · exact (hvw.1 hfree).elim
      · refine ⟨Pi.single e 1 + x, ?_, ?_⟩
        · intro a ha
          by_cases hae : a = e
          · simpa [hae] using he
          · apply hx a
            intro hxa
            apply ha
            simp [Pi.single_apply, hae, hxa]
        · rw [map_add, boundary_single, hbx]
          rcases hjoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · funext t
            exact f2_add_add_cancel_middle _ _ _
          · funext t
            exact f2_add_add_cancel_first _ _ _

lemma isForestSet_iff_f2Independent (G : LabelledMultigraph) (A : Set G.Edge) :
    G.IsForestSet A ↔ F2Independent G A := by
  classical
  constructor
  · intro hA x hx hzero
    funext e
    change x e = (0 : F2)
    by_contra hxe
    have heA : e ∈ A := hx e hxe
    have hconn : ¬ (G.connectionGraph G.freeBoundary
        (G.setConfig (A \ {e}))).Reachable (G.source e) (G.target e) := by
      intro hr
      unfold IsForestSet IsOpenForest at hA
      apply hA e (by simp [setConfig, heA])
      unfold endpointsConnectedWithout
      rwa [G.withEdge_false_setConfig]
    let H := G.connectionGraph G.freeBoundary (G.setConfig (A \ {e}))
    let p : G.Vertex → F2 := fun v => if H.Reachable (G.source e) v then 1 else 0
    have hz : (∑ a, coboundary G p a * x a) = 0 := by
      rw [dot_coboundary_boundary]
      simp [hzero]
    have hterms (a : G.Edge) : coboundary G p a * x a =
        if a = e then x e else 0 := by
      by_cases hae : a = e
      · subst a
        have hs : H.Reachable (G.source e) (G.source e) := SimpleGraph.Reachable.refl _
        have ht : ¬ H.Reachable (G.source e) (G.target e) := hconn
        simp [coboundary_apply, p, hs, ht]
      · rw [if_neg hae]
        by_cases hxa : x a = 0
        · simp [hxa]
        · have haA : a ∈ A := hx a hxa
          have hopen : (G.setConfig (A \ {e})) a = true := by
            simp [setConfig, haA, hae]
          have hadj : H.Adj (G.source a) (G.target a) := by
            refine ⟨?_, Or.inr ⟨a, hopen, Or.inl ⟨rfl, rfl⟩⟩⟩
            intro hst
            unfold IsForestSet IsOpenForest at hA
            apply hA a (by simp [setConfig, haA])
            unfold endpointsConnectedWithout
            rw [G.withEdge_false_setConfig, ← hst]
          have hr : H.Reachable (G.source e) (G.source a) ↔
              H.Reachable (G.source e) (G.target a) :=
            ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
          have hpa : p (G.source a) = p (G.target a) := by
            unfold p
            by_cases hs : H.Reachable (G.source e) (G.source a)
            · rw [if_pos hs, if_pos (hr.mp hs)]
            · rw [if_neg hs, if_neg (fun ht => hs (hr.mpr ht))]
          rw [coboundary_apply, hpa, CharTwo.add_self_eq_zero, zero_mul]
    have heq : x e = 0 := by
      calc
        x e = ∑ a, if a = e then x e else 0 := by simp
        _ = ∑ a, coboundary G p a * x a :=
          Finset.sum_congr rfl fun a _ => (hterms a).symm
        _ = 0 := hz
    exact hxe heq
  · intro hlin
    unfold IsForestSet IsOpenForest
    intro e he hconn
    have heA : e ∈ A := by simpa [setConfig] using he
    obtain ⟨w⟩ := hconn
    have hcfg : withEdge e false (G.setConfig A) = G.setConfig (A \ {e}) :=
      G.withEdge_false_setConfig e A
    rw [hcfg] at w
    obtain ⟨y, hy, hby⟩ := exists_chain_boundary_of_walk G
      (G.setConfig (A \ {e})) w
    let x : G.Edge → F2 := y + Pi.single e 1
    have hxe : x e = 1 := by
      have hye : y e = 0 := by
        by_contra hye
        have := hy e hye
        simp [setConfig] at this
      simp [x, hye]
    have hxzero : boundary G x = 0 := by
      rw [show x = y + Pi.single e 1 from rfl, map_add, hby, boundary_single]
      funext v
      exact f2_add_self_twice _ _
    have hxsupport : ∀ a, x a ≠ 0 → a ∈ A := by
      intro a ha
      by_cases hae : a = e
      · simpa [hae] using heA
      · have hya : y a ≠ 0 := by
          intro hya
          apply ha
          simp [x, hya, Pi.single_apply, hae]
        have hyaopen := hy a hya
        have : a ∈ A \ {e} := by simpa [setConfig] using hyaopen
        exact this.1
    have := hlin x hxsupport hxzero
    have : x e = 0 := by rw [this]; rfl
    rw [hxe] at this
    exact one_ne_zero this


/-- An independent connected spanning subgraph is a base of the cycle matroid. -/
lemma isBase_of_indep_preconnected (G : LabelledMultigraph) {B : Set G.Edge}
    (hI : G.cycleMatroid.Indep B)
    (hconn : (G.connectionGraph G.freeBoundary (G.setConfig B)).Preconnected) :
    G.cycleMatroid.IsBase B := by
  classical
  rw [Matroid.isBase_iff_maximal_indep, maximal_iff]
  refine ⟨hI, fun J hJ hBJ => le_antisymm hBJ ?_⟩
  intro e heJ
  by_contra heB
  have hins : G.cycleMatroid.Indep (insert e B) :=
    hJ.subset (Set.insert_subset_iff.mpr ⟨heJ, hBJ⟩)
  have hforest := (G.cycleMatroid_indep (insert e B)).mp hins
  apply hforest e (by simp [setConfig])
  unfold endpointsConnectedWithout
  have hcfg : withEdge e false (G.setConfig (insert e B)) = G.setConfig B := by
    funext a
    by_cases hae : a = e
    · subst a
      simp [withEdge, setConfig, heB]
    · simp [withEdge, setConfig, hae]
  rw [hcfg]
  exact hconn _ _

/-- Bases of a connected labelled graph are exactly its connected spanning
forests. This continues to include loops and parallel labels. -/
lemma preconnected_of_isBase (G : LabelledMultigraph)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    {B : Set G.Edge} (hB : G.cycleMatroid.IsBase B) :
    (G.connectionGraph G.freeBoundary (G.setConfig B)).Preconnected := by
  intro u v
  apply (G.reachable_setConfig_iff_of_isBasis hB.isBasis_ground u v).mpr
  simpa using hconn u v

/-- Matroid-dual independence is precisely connectedness of the complementary
edge subgraph, for a connected primal graph. -/
lemma dual_indep_iff_preconnected_compl (G : LabelledMultigraph)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (A : Set G.Edge) :
    (G.cycleMatroid)✶.Indep A ↔
      (G.connectionGraph G.freeBoundary (G.setConfig Aᶜ)).Preconnected := by
  classical
  constructor
  · intro hA
    obtain ⟨B, hB, hdisj⟩ := (Matroid.dual_indep_iff_exists (M := G.cycleMatroid)
      (I := A) (by simp)).mp hA
    have hBA : B ⊆ Aᶜ := by
      intro e heB heA
      exact Set.disjoint_left.mp hdisj heA heB
    intro u v
    exact (preconnected_of_isBase G hconn hB u v).mono
      (G.connectionGraph_mono (G.setConfig_mono hBA))
  · intro hA
    obtain ⟨B, hB⟩ := G.cycleMatroid.exists_isBasis Aᶜ
    have hBconn : (G.connectionGraph G.freeBoundary (G.setConfig B)).Preconnected := by
      intro u v
      exact (G.reachable_setConfig_iff_of_isBasis hB u v).mpr (hA u v)
    have hBase : G.cycleMatroid.IsBase B := isBase_of_indep_preconnected G hB.indep hBconn
    apply (Matroid.dual_indep_iff_exists (M := G.cycleMatroid)
      (I := A) (by simp)).mpr
    refine ⟨B, hBase, Set.disjoint_left.mpr ?_⟩
    intro e heA heB
    exact (hB.subset heB) heA

lemma cycleMatroid_indep_iff_f2Independent (G : LabelledMultigraph)
    (A : Set G.Edge) :
    G.cycleMatroid.Indep A ↔ F2Independent G A :=
  (G.cycleMatroid_indep A).trans (isForestSet_iff_f2Independent G A)

lemma coboundary_const (G : LabelledMultigraph) (c : F2) :
    coboundary G (fun _ => c) = 0 := by
  funext e
  simp [coboundary_apply, CharTwo.add_self_eq_zero]

lemma finrank_ker_coboundary (G : LabelledMultigraph) [Nonempty G.Vertex]
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected) :
    Module.finrank F2 (LinearMap.ker (coboundary G)) = 1 := by
  let v₀ : G.Vertex := Classical.choice (inferInstance : Nonempty G.Vertex)
  let ev : LinearMap.ker (coboundary G) →ₗ[F2] F2 :=
    { toFun := fun p => p.1 v₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hb : Function.Bijective ev := by
    constructor
    · intro p q hpq
      apply Subtype.ext
      funext v
      have hp : coboundary G p.1 = 0 := p.2
      have hq : coboundary G q.1 = 0 := q.2
      calc
        p.1 v = p.1 v₀ := coboundary_eq_zero_of_preconnected G hconn p.1 hp _ _
        _ = q.1 v₀ := hpq
        _ = q.1 v := (coboundary_eq_zero_of_preconnected G hconn q.1 hq _ _).symm
    · intro c
      refine ⟨⟨fun _ => c, ?_⟩, rfl⟩
      change coboundary G (fun _ => c) = 0
      exact coboundary_const G c
  let e : LinearMap.ker (coboundary G) ≃ₗ[F2] F2 := LinearEquiv.ofBijective ev hb
  calc
    _ = Module.finrank F2 F2 := e.finrank_eq
    _ = 1 := Module.finrank_self F2

lemma finrank_range_coboundary_add_one (G : LabelledMultigraph)
    [Nonempty G.Vertex]
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected) :
    Module.finrank F2 (LinearMap.range (coboundary G)) + 1 =
      Fintype.card G.Vertex := by
  have h := (coboundary G).finrank_range_add_finrank_ker
  rw [finrank_ker_coboundary G hconn] at h
  simpa only [Module.finrank_pi] using h

lemma incidence_rank_add_one (G : LabelledMultigraph) [Nonempty G.Vertex]
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected) :
    (incidence G).rank + 1 = Fintype.card G.Vertex := by
  have h := finrank_range_coboundary_add_one G hconn
  change (incidence G).transpose.rank + 1 = Fintype.card G.Vertex at h
  rwa [Matrix.rank_transpose] at h


lemma coboundary_eq_zero_of_preconnected_config (G : LabelledMultigraph)
    (ω : G.Configuration)
    (hconn : (G.connectionGraph G.freeBoundary ω).Preconnected)
    (p : G.Vertex → F2) (hp : ∀ e, ω e = true → coboundary G p e = 0)
    (u v : G.Vertex) : p u = p v := by
  have hadj : ∀ {u v : G.Vertex},
      (G.connectionGraph G.freeBoundary ω).Adj u v → p u = p v := by
    intro u v huv
    rcases huv.2 with hfree | ⟨e, he, hjoin⟩
    · exact (huv.1 hfree).elim
    · have hz : p (G.source e) + p (G.target e) = 0 := by
        rw [← coboundary_apply G]
        exact hp e he
      have hadd (a b : F2) (hab : a + b = 0) : a = b := CharTwo.add_eq_zero.mp hab
      rcases hjoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadd _ _ hz
      · exact (hadd _ _ hz).symm
  obtain ⟨w⟩ := hconn u v
  induction w with
  | nil => rfl
  | cons h w ih => exact (hadj h).trans ih

/-- A finite cellular two-complex on the sphere. The final field is the local
cell condition `∂₁ ∘ ∂₂ = 0`: every face boundary has even degree at every
vertex, summed over arbitrary face chains. It is not a matroid hypothesis. -/
structure CellularSphere (P : LabelledDualPair) : Prop where
  nonemptyVertex : Nonempty P.Vertex
  nonemptyFace : Nonempty P.Face
  primal_preconnected :
    (P.primal.connectionGraph P.primal.freeBoundary P.primal.allOpen).Preconnected
  dual_preconnected :
    (P.faceDual.connectionGraph P.faceDual.freeBoundary P.faceDual.allOpen).Preconnected
  euler : Fintype.card P.Face + Fintype.card P.Vertex = Fintype.card P.Edge + 2
  boundary_boundary : ∀ q : P.Face → F2,
    boundary P.primal (coboundary P.faceDual q) = 0

namespace LabelledDualPair

lemma boundary_faceDual_coboundary_primal (P : LabelledDualPair)
    (hS : CellularSphere P) (p : P.primal.Vertex → F2) :
    boundary P.faceDual (coboundary P.primal p) = 0 := by
  classical
  funext f
  let q : P.faceDual.Vertex → F2 := Pi.single f 1
  have hz (q : P.faceDual.Vertex → F2) :
      (∑ e, coboundary P.primal p e * coboundary P.faceDual q e) = 0 := by
    calc
      _ = ∑ v, p v * boundary P.primal (coboundary P.faceDual q) v :=
        dot_coboundary_boundary P.primal p _
      _ = 0 := by
        have hb := hS.boundary_boundary q
        change boundary P.primal (coboundary P.faceDual q) = 0 at hb
        rw [hb]
        simp
  have hleft : (∑ e, coboundary P.faceDual q e * coboundary P.primal p e) = 0 := by
    calc
      _ = ∑ e, coboundary P.primal p e * coboundary P.faceDual q e := by
        apply Finset.sum_congr rfl
        intro e _
        exact mul_comm _ _
      _ = 0 := hz q
  have hright : (∑ f', q f' * boundary P.faceDual (coboundary P.primal p) f') = 0 := by
    calc
      _ = ∑ e, coboundary P.faceDual q e * coboundary P.primal p e :=
        (dot_coboundary_boundary P.faceDual q _).symm
      _ = 0 := hleft
  have hsingle (g : P.faceDual.Vertex → F2) : (∑ f', q f' * g f') = g f := by
    classical
    simp [q, Pi.single_apply]
  calc
    _ = ∑ f', q f' * boundary P.faceDual (coboundary P.primal p) f' :=
      (hsingle _).symm
    _ = 0 := hright

/-- On a cellular sphere, primal cuts are exactly the cycles of the face dual.
The proof uses only incidence adjoints, connectivity, and Euler rank counts. -/
lemma range_coboundary_primal_eq_ker_boundary_faceDual (P : LabelledDualPair)
    (hS : CellularSphere P) :
    LinearMap.range (coboundary P.primal) =
      LinearMap.ker (boundary P.faceDual) := by
  letI : Nonempty P.primal.Vertex := hS.nonemptyVertex
  letI : Nonempty P.faceDual.Vertex := hS.nonemptyFace
  apply Submodule.eq_of_le_of_finrank_le
  · intro x hx
    obtain ⟨p, rfl⟩ := hx
    exact boundary_faceDual_coboundary_primal P hS p
  · have hs := finrank_range_coboundary_add_one P.primal hS.primal_preconnected
    change Module.finrank F2 (LinearMap.range (coboundary P.primal)) + 1 =
      Fintype.card P.Vertex at hs
    have hd := incidence_rank_add_one P.faceDual hS.dual_preconnected
    change Module.finrank F2 (LinearMap.range (boundary P.faceDual)) + 1 =
      Fintype.card P.Face at hd
    have hn := (boundary P.faceDual).finrank_range_add_finrank_ker
    simp only [Module.finrank_pi] at hn
    change Module.finrank F2 (LinearMap.range (boundary P.faceDual)) +
      Module.finrank F2 (LinearMap.ker (boundary P.faceDual)) = Fintype.card P.Edge at hn
    have he := hS.euler
    let s : ℕ := Module.finrank F2 (LinearMap.range (coboundary P.primal))
    let r : ℕ := Module.finrank F2 (LinearMap.range (boundary P.faceDual))
    let k : ℕ := Module.finrank F2 (LinearMap.ker (boundary P.faceDual))
    change s + 1 = Fintype.card P.Vertex at hs
    change r + 1 = Fintype.card P.Face at hd
    change r + k = Fintype.card P.Edge at hn
    change k ≤ s
    omega


/-- The finite plane graph criterion: a dual edge set is acyclic exactly when
its complementary primal edge set connects every pair of vertices. -/
lemma f2Independent_faceDual_iff_preconnected_compl (P : LabelledDualPair)
    (hS : CellularSphere P) (A : Set P.primal.Edge) :
    F2Independent P.faceDual A ↔
      (P.primal.connectionGraph P.primal.freeBoundary
        (P.primal.setConfig Aᶜ)).Preconnected := by
  classical
  have hspace := range_coboundary_primal_eq_ker_boundary_faceDual P hS
  constructor
  swap
  · intro hlin
    intro x hx hzero
    have hxker : x ∈ LinearMap.ker (boundary P.faceDual) := hzero
    rw [← hspace] at hxker
    obtain ⟨p, hp⟩ := hxker
    rw [← hp]
    have hpzero : ∀ e, P.primal.setConfig Aᶜ e = true →
        coboundary P.primal p e = 0 := by
      intro e he
      rw [hp]
      by_contra hxe
      have heA : e ∈ A := hx e hxe
      have heC : e ∈ Aᶜ := by simpa [LabelledMultigraph.setConfig] using he
      exact heC heA
    have hpconst (u v : P.primal.Vertex) : p u = p v :=
      coboundary_eq_zero_of_preconnected_config P.primal
        (P.primal.setConfig Aᶜ) hlin p hpzero u v
    funext e
    change coboundary P.primal p e = (0 : F2)
    rw [coboundary_apply, hpconst, CharTwo.add_self_eq_zero]
  · intro hconn
    by_contra hpre
    unfold SimpleGraph.Preconnected at hpre
    push_neg at hpre
    obtain ⟨u, v, huv⟩ := hpre
    let H := P.primal.connectionGraph P.primal.freeBoundary (P.primal.setConfig Aᶜ)
    let p : P.primal.Vertex → F2 := fun z => if H.Reachable u z then 1 else 0
    have hpu : p u = 1 := by simp [p, SimpleGraph.Reachable.refl]
    have huv' : ¬ H.Reachable u v := huv
    have hpv : p v = 0 := by simp [p, huv']
    have hpne : p u ≠ p v := by rw [hpu, hpv]; exact one_ne_zero
    let x : P.primal.Edge → F2 := coboundary P.primal p
    have hxne : x ≠ 0 := by
      intro hx
      apply hpne
      apply coboundary_eq_zero_of_preconnected P.primal hS.primal_preconnected p
      exact hx
    have hxsupport : ∀ e, x e ≠ 0 → e ∈ A := by
      intro e hxe
      by_contra heA
      have hopen : P.primal.setConfig Aᶜ e = true := by
        simp [LabelledMultigraph.setConfig, heA]
      have hadj : H.Adj (P.primal.source e) (P.primal.target e) := by
        by_cases hst : P.primal.source e = P.primal.target e
        · exfalso
          apply hxe
          change coboundary P.primal p e = (0 : F2)
          calc
            _ = p (P.primal.source e) + p (P.primal.target e) :=
              coboundary_apply P.primal p e
            _ = 0 := by rw [hst, CharTwo.add_self_eq_zero]
        · exact ⟨hst, Or.inr ⟨e, hopen, Or.inl ⟨rfl, rfl⟩⟩⟩
      have hr : H.Reachable u (P.primal.source e) ↔
          H.Reachable u (P.primal.target e) :=
        ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
      have hpe : p (P.primal.source e) = p (P.primal.target e) := by
        unfold p
        by_cases hs : H.Reachable u (P.primal.source e)
        · rw [if_pos hs, if_pos (hr.mp hs)]
        · rw [if_neg hs, if_neg (fun ht => hs (hr.mpr ht))]
      apply hxe
      change coboundary P.primal p e = (0 : F2)
      calc
        _ = p (P.primal.source e) + p (P.primal.target e) :=
          coboundary_apply P.primal p e
        _ = 0 := by rw [hpe, CharTwo.add_self_eq_zero]
    have hxzero : boundary P.faceDual x = 0 := by
      have hxmem : x ∈ LinearMap.range (coboundary P.primal) := ⟨p, rfl⟩
      rw [hspace] at hxmem
      exact hxmem
    exact hxne (hconn x hxsupport hxzero)

/-- **Graphic duality from a finite cellular sphere.** No field of `hS`
mentions matroid independence, matroid duality, or an Euler relation for open
subconfigurations. Those are proved here from the two-cell geometry. -/
theorem graphicDualCertificate_of_cellularSphere (P : LabelledDualPair)
    (hS : CellularSphere P) : P.GraphicDualCertificate := by
  refine ⟨?_, hS.nonemptyFace, hS.dual_preconnected⟩
  apply Matroid.ext_indep (M₁ := (P.primal.cycleMatroid)✶)
    (M₂ := P.faceDual.cycleMatroid) (by simp only [Matroid.dual_ground, cycleMatroid_ground]; rfl)
  intro A hA
  change Set P.Edge at A
  calc
    _ ↔ (P.primal.connectionGraph P.primal.freeBoundary
        (P.primal.setConfig Aᶜ)).Preconnected :=
      dual_indep_iff_preconnected_compl P.primal hS.primal_preconnected A
    _ ↔ F2Independent P.faceDual A :=
      (f2Independent_faceDual_iff_preconnected_compl P hS A).symm
    _ ↔ P.faceDual.cycleMatroid.Indep A :=
      (cycleMatroid_indep_iff_f2Independent P.faceDual A).symm

/-- The configurationwise Euler identity is a consequence, not an input. -/
theorem componentCount_dual_add_card_vertices_of_cellularSphere
    (P : LabelledDualPair) (hS : CellularSphere P) (ω : P.Edge → Bool) :
    P.faceDual.componentCount P.faceDual.freeBoundary
        (FK.Configuration.dualConfig (Equiv.refl P.Edge) ω) + Fintype.card P.Vertex =
      P.primal.componentCount P.primal.freeBoundary ω + 1 + openCard ω :=
  P.componentCount_dual_add_card_vertices (graphicDualCertificate_of_cellularSphere P hS) ω

/-- Actual normalized FK duality for a labelled cellular sphere. -/
theorem actual_fkPMF_duality_of_cellularSphere (P : LabelledDualPair)
    (hS : CellularSphere P) (q p : NNReal) (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (FK.Configuration.dualEquiv (Equiv.refl P.Edge))
        (P.primal.fkPMF hq hp₁.le P.primal.freeBoundary) =
      P.faceDual.fkPMF hq (dualParameter_le_one hq hp₁.le) P.faceDual.freeBoundary :=
  P.actual_fkPMF_graphicDual_duality (graphicDualCertificate_of_cellularSphere P hS)
    q p hq hp₀ hp₁

end LabelledDualPair

end Cellular
end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid.Cellular.Examples

open scoped BigOperators Classical
open FK.Finite.LabelledMultigraph
open FK.FinitePlane

/-- The two-gon: two vertices, two parallel labelled edges, two faces, and two
parallel dual edges. Both face assignments are exactly the face incidence of
this cellular embedding of the two-gon on the sphere. -/
def digonPair : LabelledDualPair where
  Vertex := Bool
  Face := Bool
  Edge := Bool
  source _ := false
  target _ := true
  dualSource _ := false
  dualTarget _ := true

lemma primal_preconnected_digonPair :
    (digonPair.primal.connectionGraph digonPair.primal.freeBoundary
      digonPair.primal.allOpen).Preconnected := by
  change (twoEdgeCycle.connectionGraph twoEdgeCycle.freeBoundary
    twoEdgeCycle.allOpen).Preconnected
  exact isLabelledCycle_twoEdgeCycle.preconnected

lemma dual_preconnected_digonPair :
    (digonPair.faceDual.connectionGraph digonPair.faceDual.freeBoundary
      digonPair.faceDual.allOpen).Preconnected := by
  change (twoEdgeCycle.connectionGraph twoEdgeCycle.freeBoundary
    twoEdgeCycle.allOpen).Preconnected
  exact isLabelledCycle_twoEdgeCycle.preconnected

/-- The digon is a concrete inhabited instance of the cellular input. -/
theorem cellularSphere_digonPair : CellularSphere digonPair := by
  refine ⟨⟨false⟩, ⟨false⟩, primal_preconnected_digonPair,
    dual_preconnected_digonPair, by decide, ?_⟩
  intro q
  change (twoEdgeCycle.Vertex → F2) at q
  change boundary twoEdgeCycle (coboundary twoEdgeCycle q) = 0
  funext v
  change boundary twoEdgeCycle (coboundary twoEdgeCycle q) v = (0 : F2)
  rw [boundary_apply twoEdgeCycle]
  simp_rw [coboundary_apply twoEdgeCycle]
  have hc : (@Finset.univ Bool twoEdgeCycle.fintypeEdge).card = 2 := by decide
  have htwo : (2 : F2) = 0 := by decide
  cases v <;>
    simp [twoEdgeCycle, CharTwo.add_self_eq_zero, add_comm, add_left_comm, add_assoc, hc, htwo]

/-- The new general theorem produces genuine graphic matroid duality for the
digon; no matroid-equality premise occurs in `cellularSphere_digonPair`. -/
theorem graphicDualCertificate_digonPair : digonPair.GraphicDualCertificate :=
  LabelledDualPair.graphicDualCertificate_of_cellularSphere digonPair cellularSphere_digonPair

end FK.Finite.PlaneMatroid.Cellular.Examples


/-!
## Realizing cellular spheres by rotation systems

A rotation system is a permutation `rotation` of oriented darts which preserves
vertices and is transitive on the darts at each vertex.  If `reverse` reverses a
dart, the faces are the cycles of `rotation * reverse`.  This definition needs
no independent matroid, independence, or duality hypothesis.
-/

namespace FK.Finite.PlaneMatroid.Cellular.Rotation

open scoped BigOperators Classical
open FK.Finite.LabelledMultigraph
open FK.FinitePlane
open FK.Finite.Conditional
open FK.FiniteFiber
open Equiv.Perm

variable (G : LabelledMultigraph)

/-- The two oriented darts on a labelled edge. -/
abbrev Dart := G.Edge × Bool

/-- The vertex at which a dart is based. -/
def vertex : Dart G → G.Vertex
  | (e, false) => G.source e
  | (e, true) => G.target e

/-- Reversal of the orientation of a dart. -/
def reverse : Equiv.Perm (Dart G) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv d := by rcases d with ⟨e, b⟩; cases b <;> rfl
  right_inv d := by rcases d with ⟨e, b⟩; cases b <;> rfl

@[simp] lemma reverse_reverse (d : Dart G) : reverse G (reverse G d) = d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

@[simp] lemma reverse_edge (d : Dart G) : (reverse G d).1 = d.1 := rfl

@[simp] lemma vertex_reverse (d : Dart G) :
    vertex G (reverse G d) = vertex G (d.1, !d.2) := rfl

/-- A genuine finite combinatorial rotation system.  `sameCycle_rotation` is the
local cyclic-order condition: the darts at one vertex form one rotation cycle. -/
structure RotationSystem where
  rotation : Equiv.Perm (Dart G)
  vertex_rotation : ∀ d, vertex G (rotation d) = vertex G d
  sameCycle_rotation : ∀ d d', vertex G d = vertex G d' → rotation.SameCycle d d'

namespace RotationSystem

variable {G : LabelledMultigraph} (R : RotationSystem G)

/-- Face traversal: reverse the current dart, then rotate at the vertex reached. -/
def facePerm : Equiv.Perm (Dart G) := R.rotation * reverse G

/-- Faces are precisely the cycles of the face-traversal permutation. -/
def Face := Quotient (Equiv.Perm.SameCycle.setoid R.facePerm)

/-- The face represented by a dart. -/
def faceOf (d : Dart G) : R.Face := Quotient.mk (Equiv.Perm.SameCycle.setoid R.facePerm) d

lemma faceOf_eq_iff {d d' : Dart G} :
    R.faceOf d = R.faceOf d' ↔ R.facePerm.SameCycle d d' := Quotient.eq

lemma facePerm_reverse (d : Dart G) : R.facePerm (reverse G d) = R.rotation d := by
  simp [facePerm]

/-- Rotation and reversal of corresponding darts represent the same face. -/
lemma faceOf_reverse_eq_faceOf_rotation (d : Dart G) :
    R.faceOf (reverse G d) = R.faceOf (R.rotation d) := by
  rw [faceOf_eq_iff]
  refine ⟨1, ?_⟩
  simp [facePerm_reverse]

/-- The plane-dual pair constructed from the rotation, not postulated separately. -/
noncomputable abbrev dualPair : LabelledDualPair := by
  classical
  letI : Finite R.Face := Finite.of_surjective R.faceOf
    (fun f => ⟨f.out, Quotient.out_eq f⟩)
  letI : Fintype R.Face := Fintype.ofFinite R.Face
  exact
    { Vertex := G.Vertex
      Face := R.Face
      Edge := G.Edge
      source := G.source
      target := G.target
      dualSource := fun e => R.faceOf (e, false)
      dualTarget := fun e => R.faceOf (e, true) }

@[simp] lemma dualPair_primal : R.dualPair.primal = G := rfl

/-- The dual endpoints are the two faces represented by the two orientations. -/
lemma faceDual_joins (e : G.Edge) :
    R.dualPair.faceDual.Joins e (R.faceOf (e, false)) (R.faceOf (e, true)) := by
  exact Or.inl ⟨rfl, rfl⟩

/-- Reversing a dart gives aReachable step in the all-open face-dual graph. -/
lemma reachable_faceOf_reverse (d : Dart G) :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      R.dualPair.faceDual.allOpen).Reachable (R.faceOf d) (R.faceOf (reverse G d)) := by
  by_cases h : R.faceOf d = R.faceOf (reverse G d)
  · rw [h]
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    refine ⟨h, Or.inr ⟨d.1, rfl, ?_⟩⟩
    rcases d with ⟨e, b⟩
    cases b
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Reindexing a vertex-weighted dart sum by the vertex rotation leaves it fixed. -/
lemma vertexSum_rotation (v : G.Vertex) (a : Dart G → F2) :
    (∑ d, if vertex G d = v then a (R.rotation d) else 0) =
      ∑ d, if vertex G d = v then a d else 0 := by
  classical
  have hs := Equiv.sum_comp R.rotation
    (fun d => if vertex G d = v then a d else 0)
  simpa only [R.vertex_rotation] using hs

/-- Expanding a sum over darts at a vertex into its two endpoint sums. -/
lemma sum_darts_vertex (v : G.Vertex) (a : Dart G → F2) :
    (∑ d, if vertex G d = v then a d else 0) =
      ∑ e, ((if v = G.source e then a (e, false) else 0) +
        (if v = G.target e then a (e, true) else 0)) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_bool]
  simp [vertex, eq_comm, add_comm]

/-- The cellular boundary at a vertex is the sum of the two face chains on all
incident darts.  This expansion is valid for loops: both orientations then occur
in both endpoint contributions, exactly as the `F2` incidence requires. -/
lemma boundary_faceDual_coboundary_apply (R : RotationSystem G)
    (q : R.Face → F2) (v : G.Vertex) :
    boundary R.dualPair.primal (coboundary R.dualPair.faceDual q) v =
      (∑ d, if vertex G d = v then q (R.faceOf d) else 0) +
      (∑ d, if vertex G d = v then q (R.faceOf (reverse G d)) else 0) := by
  classical
  have hb := boundary_apply R.dualPair.primal (coboundary R.dualPair.faceDual q) v
  have hc (e : G.Edge) : coboundary R.dualPair.faceDual q e =
      q (R.faceOf (e, false)) + q (R.faceOf (e, true)) := by
    exact coboundary_apply R.dualPair.faceDual q e
  rw [hb]
  rw [sum_darts_vertex (G := G), sum_darts_vertex (G := G)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [hc e]
  change ((if v = G.source e then q (R.faceOf (e, false)) +
      q (R.faceOf (e, true)) else 0) +
    (if v = G.target e then q (R.faceOf (e, false)) +
      q (R.faceOf (e, true)) else 0)) = _
  by_cases hs : v = G.source e <;> by_cases ht : v = G.target e <;>
    simp_all [reverse, add_comm, add_left_comm, add_assoc]

/-- **The two-cell boundary identity is automatic for a rotation system.**  At
each vertex the two sums coincide: first `faceOf_reverse_eq_faceOf_rotation`,
then bijective reindexing by the vertex rotation.  Their `F2` sum is zero. -/
lemma boundary_faceDual_coboundary (R : RotationSystem G) (q : R.Face → F2) :
    boundary R.dualPair.primal (coboundary R.dualPair.faceDual q) = 0 := by
  classical
  simp only [dualPair_primal]
  funext v
  change boundary R.dualPair.primal (coboundary R.dualPair.faceDual q) v = (0 : F2)
  rw [boundary_faceDual_coboundary_apply R q v]
  have hface :
      (∑ d, if vertex G d = v then q (R.faceOf (reverse G d)) else 0) =
        ∑ d, if vertex G d = v then q (R.faceOf (R.rotation d)) else 0 := by
    apply Finset.sum_congr rfl
    intro d _
    rw [R.faceOf_reverse_eq_faceOf_rotation]
  rw [hface, R.vertexSum_rotation v (fun d => q (R.faceOf d)),
    CharTwo.add_self_eq_zero]

/-- A single rotation step is a reachability step in the face dual. -/
lemma reachable_faceOf_rotation (R : RotationSystem G) (d : Dart G) :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      R.dualPair.faceDual.allOpen).Reachable (R.faceOf d) (R.faceOf (R.rotation d)) := by
  rw [← R.faceOf_reverse_eq_faceOf_rotation]
  exact R.reachable_faceOf_reverse d

/-- Two darts in the same local rotation cycle are connected through the face dual. -/
lemma reachable_faceOf_sameCycle (R : RotationSystem G) {d d' : Dart G}
    (h : R.rotation.SameCycle d d') :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      R.dualPair.faceDual.allOpen).Reachable (R.faceOf d) (R.faceOf d') := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero =>
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq]
      exact @SimpleGraph.Reachable.refl R.dualPair.faceDual.Vertex _ (R.faceOf d)
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans (R.reachable_faceOf_rotation _)

/-- A primal walk lifts to a reachability path between any darts based at its
endpoints.  Every edge traversal is dart reversal; every change of dart at a
vertex is a rotation-cycle traversal. -/
lemma reachable_faceOf_of_walk (R : RotationSystem G) {u v : G.Vertex}
    (w : (G.connectionGraph G.freeBoundary G.allOpen).Walk u v) :
    ∀ {d d' : Dart G}, vertex G d = u → vertex G d' = v →
      (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
        R.dualPair.faceDual.allOpen).Reachable (R.faceOf d) (R.faceOf d') := by
  induction w with
  | nil =>
      intro d d' hd hd'
      apply R.reachable_faceOf_sameCycle
      apply R.sameCycle_rotation
      rw [hd, hd']
  | @cons u v z huv w ih =>
      intro d d' hd hd'
      rcases huv.2 with hfree | ⟨e, _, hjoin⟩
      · exact (huv.1 hfree).elim
      · rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · have hdu : vertex G d = vertex G (e, false) := by
            rw [hd]
            exact hs.symm
          have hda := R.reachable_faceOf_sameCycle (R.sameCycle_rotation d (e, false) hdu)
          have hab : (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
              R.dualPair.faceDual.allOpen).Reachable (R.faceOf (e, false))
                (R.faceOf (e, true)) := by
            simpa [reverse] using R.reachable_faceOf_reverse (e, false)
          have hbd' := ih (d := (e, true)) (d' := d') ht hd'
          exact (hda.trans hab).trans hbd'
        · have hdu : vertex G d = vertex G (e, true) := by
            rw [hd]
            exact ht.symm
          have hda := R.reachable_faceOf_sameCycle (R.sameCycle_rotation d (e, true) hdu)
          have hab : (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
              R.dualPair.faceDual.allOpen).Reachable (R.faceOf (e, true))
                (R.faceOf (e, false)) := by
            simpa [reverse] using R.reachable_faceOf_reverse (e, true)
          have hbd' := ih (d := (e, false)) (d' := d') hs hd'
          exact (hda.trans hab).trans hbd'

/-- Connectivity of a primal rotation system gives genuine all-open connectivity
of its constructed face dual. -/
lemma allOpen_preconnected (R : RotationSystem G)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected) :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      R.dualPair.faceDual.allOpen).Preconnected := by
  intro f g
  refine Quotient.inductionOn f (fun d => Quotient.inductionOn g (fun d' => ?_))
  obtain ⟨w⟩ := hconn (vertex G d) (vertex G d')
  exact R.reachable_faceOf_of_walk w rfl rfl

end RotationSystem

/-- A connected spherical combinatorial embedding.  The local rotation axioms
encode the embedding; `euler` is precisely its genus-zero relation.  Nothing in
this structure mentions a matroid or matroid duality. -/
structure RotationSphere (G : LabelledMultigraph) extends RotationSystem G where
  nonemptyVertex : Nonempty G.Vertex
  nonemptyDart : Nonempty (Dart G)
  primal_preconnected :
    (G.connectionGraph G.freeBoundary G.allOpen).Preconnected
  euler : @Fintype.card (RotationSystem.dualPair toRotationSystem).Face
      (RotationSystem.dualPair toRotationSystem).fintypeFace +
    Fintype.card G.Vertex = Fintype.card G.Edge + 2

namespace RotationSphere

variable {G : LabelledMultigraph} (S : RotationSphere G)

/-- The actual face dual of a spherical rotation system carries the cellular
incidence structure used by the `F2` duality theorem. -/
theorem cellularSphere : CellularSphere (RotationSystem.dualPair S.toRotationSystem) where
  nonemptyVertex := S.nonemptyVertex
  nonemptyFace := ⟨S.toRotationSystem.faceOf S.nonemptyDart.some⟩
  primal_preconnected := S.primal_preconnected
  dual_preconnected := S.toRotationSystem.allOpen_preconnected S.primal_preconnected
  euler := S.euler
  boundary_boundary := S.toRotationSystem.boundary_faceDual_coboundary

/-- **Graphic duality of an actual face dual constructed from a rotation system.**
The only surface-genus input is the Euler relation; both the cells and their
incidences are computed from the dart permutations. -/
theorem graphicDualCertificate_of_rotationSphere :
    (RotationSystem.dualPair S.toRotationSystem).GraphicDualCertificate :=
  LabelledDualPair.graphicDualCertificate_of_cellularSphere _ S.cellularSphere

/-- The configurationwise Euler/FK component identity for the constructed face
rotation dual, obtained from graphic matroid duality rather than assumed. -/
theorem componentCount_dual_add_card_vertices_of_rotationSphere (ω : G.Edge → Bool) :
    (RotationSystem.dualPair S.toRotationSystem).faceDual.componentCount
        (RotationSystem.dualPair S.toRotationSystem).faceDual.freeBoundary
        (FK.Configuration.dualConfig (Equiv.refl G.Edge) ω) + Fintype.card G.Vertex =
      G.componentCount G.freeBoundary ω + 1 + openCard ω :=
  (RotationSystem.dualPair S.toRotationSystem).componentCount_dual_add_card_vertices
    S.graphicDualCertificate_of_rotationSphere ω

end RotationSphere
end FK.Finite.PlaneMatroid.Cellular.Rotation
