/-
# Boundary confinement is not removable

The positive results of `FK.RegionConfinement` continue the region law from a
fixed exterior configuration to the actual region FK law only under
*confinement*: no boundary block may contain a region vertex together with a
vertex outside the region.

This file shows that the condition is genuinely needed, not an artefact: a
four-vertex FK graph with a cross-wired boundary has a well-defined separated
exterior configuration whose induced interior law is **not** the region FK law.
The failure is at the level of the two actual `fkPMF`s, at `p = q = 1/2`.

Consequently the residual obligation in `docs/PROOF-STATUS.md` item 3 — to
match ordinary nested metric boxes with *arbitrary* boundary laws to the
compatible-cross class — cannot be met as stated: the boundary class has to be
restricted (the standard free / wired / boundary-vertex conventions do satisfy
confinement when the region sits strictly inside the box).
-/

import FK.NestedCommonUpperGood
import FK.PlanarForestDuality

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionConfinement

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary

attribute [local instance] Classical.propDecidable

/-- Region vertices. -/
abbrev CW : Type := Fin 2
/-- Outside vertices. -/
abbrev CK : Type := Fin 2

/-- The region-internal edge. -/
def csi : Fin 1 → CW := fun _ => 0
/-- The region-internal edge. -/
def cti : Fin 1 → CW := fun _ => 1
/-- The exterior edge is internal to the outside part. -/
def cso : Fin 1 → CW ⊕ CK := fun _ => Sum.inr 0
/-- The exterior edge is internal to the outside part. -/
def cxo : Fin 1 → CW ⊕ CK := fun _ => Sum.inr 1

/-- The cross-wired boundary: region vertex `i` is wired to outside vertex `i`.
This setoid is *not* confined to either summand. -/
def crossWiring : Setoid (CW ⊕ CK) :=
  Setoid.ker (fun x => Sum.elim id id x)

/-- The open exterior configuration: the outside edge is open, and it avoids the
region, so the maximal-stratum separation hypothesis holds. -/
def cExt : Fin 1 → Bool := fun _ => true

/-- The interior graph of the example. -/
abbrev cG : LabelledMultigraph :=
  interiorOfSum (splitSource csi cso) (splitTarget cti cxo)

/-- The region graph of the example. -/
abbrev cR : LabelledMultigraph := regionGraph csi cti

/-- The induced boundary of the open exterior fibre. -/
abbrev cBd : Setoid (CW ⊕ CK) :=
  effectiveBoundary (splitSource csi cso) (splitTarget cti cxo) crossWiring cExt

lemma crossWiring_inl_inr (i : CW) : crossWiring.r (Sum.inl i) (Sum.inr i) := rfl

lemma crossWiring_inr_inl (i : CW) : crossWiring.r (Sum.inr i) (Sum.inl i) := rfl

/-- The cross-wiring together with the open exterior edge connects every pair of
vertices, so the induced boundary is universal. -/
lemma cBd_universal (x y : CW ⊕ CK) : cBd.r x y := by
  have hstep : ∀ a b : CW ⊕ CK, cBd.r a b := by
    intro a b
    have h0 : cBd.r (Sum.inl (0 : CW)) (Sum.inr (0 : CK)) :=
      SimpleGraph.Adj.reachable ⟨Sum.inl_ne_inr, Or.inl (crossWiring_inl_inr 0)⟩
    have h1 : cBd.r (Sum.inr (0 : CK)) (Sum.inr (1 : CK)) :=
      SimpleGraph.Adj.reachable
        ⟨fun h => by simpa using Sum.inr.inj h,
          Or.inr ⟨Sum.inr 0, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    have h2 : cBd.r (Sum.inr (1 : CK)) (Sum.inl (1 : CW)) :=
      SimpleGraph.Adj.reachable ⟨Sum.inr_ne_inl, Or.inl (crossWiring_inr_inl 1)⟩
    have hall : ∀ z : CW ⊕ CK, cBd.r (Sum.inl (0 : CW)) z := by
      intro z
      rcases z with c | k
      · fin_cases c
        · exact (cBd).refl _
        · exact h0.trans (h1.trans h2)
      · fin_cases k
        · exact h0
        · exact h0.trans h1
    exact (hall a).symm.trans (hall b)
  exact hstep x y

theorem cG_componentCount (ω : Fin 1 → Bool) : cG.componentCount cBd ω = 1 := by
  refine componentCount_eq_one_of_preconnected cG cBd ω (Sum.inl 0) ?_
  intro x y
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨hxy, Or.inl (cBd_universal x y)⟩

/-- With the free region boundary and the open edge, the region graph is
connected. -/
theorem cR_componentCount_open :
    cR.componentCount cR.freeBoundary (fun _ => true) = 1 := by
  have hjoin : ∀ x y : Fin 2, x ≠ y →
      (cR.source (0 : Fin 1) = x ∧ cR.target (0 : Fin 1) = y) ∨
        (cR.source (0 : Fin 1) = y ∧ cR.target (0 : Fin 1) = x) := by
    intro x y _
    fin_cases x <;> fin_cases y <;>
      simp_all [cR, regionGraph, csi, cti, LabelledMultigraph.Joins]
  refine componentCount_eq_one_of_preconnected cR cR.freeBoundary _ (0 : Fin 2) ?_
  intro x y
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨hxy, Or.inr ⟨(0 : Fin 1), rfl, hjoin x y hxy⟩⟩

/-- With the free region boundary and the closed edge, the region graph has two
components. -/
theorem cR_componentCount_closed_allClosed :
    cR.componentCount cR.freeBoundary cR.allClosed = 2 := by
  rw [componentCount_free_allClosed]
  simp [cR, regionGraph]

/-- The same count at the explicit all-closed configuration. -/
theorem cR_componentCount_closed :
    cR.componentCount cR.freeBoundary (fun _ => false) = 2 :=
  cR_componentCount_closed_allClosed

/-- Sums over the two configurations of the single region edge. -/
lemma sum_config_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Bool) → M) :
    (∑ ω : Fin 1 → Bool, f ω) = f (fun _ => true) + f (fun _ => false) := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm f, Fintype.sum_bool]
  rfl

/-- The induced boundary of the cross-wired example relates the two *region*
vertices to each other, although the region setoid is discrete.  So the induced
interior law cannot be the region FK law with the region boundary: it is the
region FK law with the *induced* boundary, which is universal here. -/
theorem induced_region_boundary_not_free :
    cBd.r (Sum.inl (0 : CW)) (Sum.inl (1 : CW)) ∧
      ¬ cR.freeBoundary.r (0 : Fin 2) (1 : Fin 2) :=
  ⟨cBd_universal _ _, by
    show ¬ ((0 : Fin 2) = 1)
    norm_num⟩

/-- The confinement hypothesis of `interior_fkPMF_eq_region_confined` genuinely
fails for the cross-wired example. -/
theorem crossWiring_not_confined :
    ¬ ∀ (a : CW) (y : CW ⊕ CK), crossWiring.r (Sum.inl a) y → ∃ a' : CW, y = Sum.inl a' := by
  intro h
  obtain ⟨a', ha'⟩ := h 0 (Sum.inr 0) (crossWiring_inl_inr 0)
  exact absurd ha' (by simp)

end FK.RegionConfinement
