/-
# The actual finite-volume FK law is DLR at its own box

This records that the hypothesis class of the random-region fibre identity is
inhabited at every box: the genuine finite-volume FK law with a constant boundary
partition satisfies the exact DLR equation at that box, with the same partition.
The statement is the reflexive case of the DLR equation, so it is a consistency
check on the class of laws to which the fibre identity applies; no limiting
argument and no nesting compatibility are used.
-/

import FK.RegionFiniteBox

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace FK.InfiniteVolume

variable {E : Type*}

/-- The genuine finite-volume FK law with a constant boundary partition is DLR at
its own box with that partition. -/
theorem finiteVolumeLaw_isDLR (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.BoundaryPartition) :
    B.IsDLR hq hp (fun _ => α) measurable_const (B.finiteVolumeLaw hq hp α) := by
  classical
  set ν : Measure B.Interior := B.graph.fkMeasure hq hp α with hν
  have : IsProbabilityMeasure ν :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp α
  have hcoe : (B.finiteVolumeLaw hq hp α : Measure (Configuration E)) =
      Measure.map (fun ω : B.Interior => B.glue (B.closedExterior, ω)) ν := rfl
  have hglue : Measurable (fun ω : B.Interior => B.glue (B.closedExterior, ω)) :=
    B.measurable_glue_const_left B.closedExterior
  have hsplit_fun : (⇑B.splitEquiv ∘ fun ω : B.Interior => B.glue (B.closedExterior, ω)) =
      Prod.mk B.closedExterior := by
    funext ω
    exact B.split_glue (B.closedExterior, ω)
  have hsplit : Measure.map B.splitEquiv (B.finiteVolumeLaw hq hp α : Measure (Configuration E))
      = (Measure.dirac B.closedExterior).prod ν := by
    rw [hcoe, Measure.map_map B.splitEquiv.measurable hglue, hsplit_fun,
      Measure.dirac_prod]
  have hext : (B.exteriorMeasure (B.finiteVolumeLaw hq hp α) : Measure B.Exterior) =
      Measure.dirac B.closedExterior := by
    rw [show (B.exteriorMeasure (B.finiteVolumeLaw hq hp α) : Measure B.Exterior) =
      ↑(ProbabilityMeasure.map (B.finiteVolumeLaw hq hp α)
        (fun ω => (B.splitEquiv ω).1)) from rfl, ProbabilityMeasure.toMeasure_map,
      show (fun z : Configuration E => (B.splitEquiv z).1) =
        Prod.fst ∘ ⇑B.splitEquiv from rfl, ← Measure.map_map measurable_fst
        B.splitEquiv.measurable]
    rw [hsplit, show Measure.map Prod.fst ((Measure.dirac B.closedExterior).prod ν) =
      ((Measure.dirac B.closedExterior).prod ν).fst from rfl, Measure.fst_prod]
  have hker : B.fkKernel hq hp (fun _ => α) measurable_const =
      ProbabilityTheory.Kernel.const B.Exterior ν := by
    ext η s _
    rw [FiniteBox.fkKernel_apply, ProbabilityTheory.Kernel.const_apply, hν]
  unfold FiniteBox.IsDLR
  rw [hext, hsplit, hker]
  exact (Measure.compProd_const (μ := Measure.dirac B.closedExterior) (ν := ν)).symm

/-! ## Axiom audit -/

#print axioms FK.InfiniteVolume.finiteVolumeLaw_isDLR

end FK.InfiniteVolume
