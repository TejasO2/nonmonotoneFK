import FK.NestedMixture.NestedBox

/-!
# The nested-box free-mass comparison

For a nested pair `B ⊆ C` of finite boxes and every increasing interior event of
the smaller box, the mass under the larger box's free finite-volume law is at
least the smaller box's own free mass.  The transport of the small box into the
region of the large box is a genuine measure identification
(`fkMeasure_free_transport_apply` plus `subBox_fkMeasure_eq_transport`), after
which the exterior mixture (`FK.NestedMixture.fkMeasure_cyl_ge_free`) gives the
inequality.
-/

open scoped Classical BigOperators ENNReal NNReal
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.SpecificationNesting

namespace FK.NestedMixture

variable {E : Type*}

/-- Sums over the same finite type agree for any two `Fintype` structures. -/
theorem finset_sum_inst_congr {α M : Type*} [AddCommMonoid M] {i₁ i₂ : Fintype α}
    (f : α → M) :
    @Finset.sum α M _ (@Finset.univ α i₁) f
      = @Finset.sum α M _ (@Finset.univ α i₂) f :=
  congrArg (fun (j : Fintype α) => @Finset.sum α M _ (@Finset.univ α j) f)
    (Subsingleton.elim i₁ i₂)

/-- The mass of an event under a finite FK law, as a sum of point masses, for an
arbitrary `Fintype` structure on the interior configuration type. -/
theorem fkMeasure_eq_sum_inst (G : LabelledMultigraph) (i : Fintype (G.Edge → Bool))
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (π : G.BoundaryPartition)
    (A : Set (G.Edge → Bool)) :
    G.fkMeasure hq hp π A
      = @Finset.sum (G.Edge → Bool) ℝ≥0∞ _ (@Finset.univ _ i)
          (fun ω => if ω ∈ A then G.fkPMF hq hp π ω else 0) := by
  letI := i
  rw [fkMeasure, PMF.toMeasure_apply_fintype]
  rfl

namespace NestedBox

variable {B C : FK.InfiniteVolume.FiniteBox E} (N : NestedBox B C)

/-- The interior event of the small box, read in the region coordinates of the
large box. -/
def cylOf (A : Set B.Interior) : Set (↥N.ide → Bool) :=
  {ζ | (fun b : B.edges => ζ (N.edgeEquiv.symm b)) ∈ A}

theorem cylOf_isUpperSet {A : Set B.Interior} (hA : IsUpperSet A) :
    IsUpperSet (N.cylOf A) := by
  intro x y hxy hx
  exact hA (fun b => hxy (N.edgeEquiv.symm b)) hx

/-- **The region sub-box law is the small box law.** -/
theorem subBox_fkMeasure_eq_transport {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (A : Set (↥N.ide → Bool)) :
    (subBox N.dom N.ide N.hdom).fkMeasure hq hp
        (subBox N.dom N.ide N.hdom).freeBoundary A
      = (B.graph.transport N.vertEquiv N.edgeEquiv).fkMeasure hq hp
          (B.graph.transport N.vertEquiv N.edgeEquiv).freeBoundary A := by
  exact fkMeasure_eq_of_source_target_eq (V := ↥N.dom) (E := ↥N.ide)
    (fun a => (⟨C.graph.source (a : C.graph.Edge), (N.hdom a).1⟩ : ↥N.dom))
    (fun a => (⟨C.graph.target (a : C.graph.Edge), (N.hdom a).2⟩ : ↥N.dom))
    (fun a => N.vertEquiv.symm (B.graph.source (N.edgeEquiv a)))
    (fun a => N.vertEquiv.symm (B.graph.target (N.edgeEquiv a)))
    N.transport_source_eq.symm N.transport_target_eq.symm hq hp _ A

/-- **Nested free-mass monotonicity.**  At `q ≥ 1`, every increasing interior
event of a sub-box has at most the mass under the larger box's free law. -/
theorem nested_free_mass_le {q p : NNReal} (hq1 : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    {A : Set B.Interior} (hA : IsUpperSet A) :
    B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le B.graph.freeBoundary A
      ≤ C.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le C.graph.freeBoundary
          {x : C.Interior | (fun a : ↥N.ide => x a.1) ∈ N.cylOf A} := by
  classical
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hAmeas : MeasurableSet A := Set.Finite.measurableSet (Set.toFinite A)
  have h1 : B.graph.fkMeasure hq hp1.le B.graph.freeBoundary A
      = (B.graph.transport N.vertEquiv N.edgeEquiv).fkMeasure hq hp1.le
          (B.graph.transport N.vertEquiv N.edgeEquiv).freeBoundary (N.cylOf A) :=
    fkMeasure_free_transport_apply B.graph N.vertEquiv N.edgeEquiv hq hp0 hp1 hAmeas
  have h2 : (B.graph.transport N.vertEquiv N.edgeEquiv).fkMeasure hq hp1.le
        (B.graph.transport N.vertEquiv N.edgeEquiv).freeBoundary (N.cylOf A)
      = (subBox N.dom N.ide N.hdom).fkMeasure hq hp1.le
          (subBox N.dom N.ide N.hdom).freeBoundary (N.cylOf A) :=
    (N.subBox_fkMeasure_eq_transport hq hp1.le (N.cylOf A)).symm
  have h3 : (subBox N.dom N.ide N.hdom).fkMeasure hq hp1.le
        (subBox N.dom N.ide N.hdom).freeBoundary (N.cylOf A)
      ≤ C.graph.fkMeasure hq hp1.le C.graph.freeBoundary
          {ω : C.graph.Configuration | restrictI N.ide ω ∈ N.cylOf A} :=
    fkMeasure_cyl_ge_free (G := C.graph) (dom := N.dom) (I := N.ide) (hdom := N.hdom)
      (α := C.graph.freeBoundary) (q := q) (p := p) hq1 hp0 hp1 (N.cylOf_isUpperSet hA)
  exact h1.trans_le (h2.trans_le h3)

/-- **Nested mass monotonicity for an arbitrary large-box boundary condition.**
At `q ≥ 1` the small box's free mass of an increasing event is bounded by the
large box's cylinder mass under *any* boundary setoid, in particular under the
paper's boundary-only wired convention. -/
theorem nested_mass_le_of_any_boundary {q p : NNReal} (hq1 : 1 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) (α : C.graph.BoundaryPartition) {A : Set B.Interior}
    (hA : IsUpperSet A) :
    B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le B.graph.freeBoundary A
      ≤ C.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq1) hp1.le α
          {x : C.Interior | (fun a : ↥N.ide => x a.1) ∈ N.cylOf A} := by
  classical
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hAmeas : MeasurableSet A := Set.Finite.measurableSet (Set.toFinite A)
  have h1 : B.graph.fkMeasure hq hp1.le B.graph.freeBoundary A
      = (B.graph.transport N.vertEquiv N.edgeEquiv).fkMeasure hq hp1.le
          (B.graph.transport N.vertEquiv N.edgeEquiv).freeBoundary (N.cylOf A) :=
    fkMeasure_free_transport_apply B.graph N.vertEquiv N.edgeEquiv hq hp0 hp1 hAmeas
  have h2 : (B.graph.transport N.vertEquiv N.edgeEquiv).fkMeasure hq hp1.le
        (B.graph.transport N.vertEquiv N.edgeEquiv).freeBoundary (N.cylOf A)
      = (subBox N.dom N.ide N.hdom).fkMeasure hq hp1.le
          (subBox N.dom N.ide N.hdom).freeBoundary (N.cylOf A) :=
    (N.subBox_fkMeasure_eq_transport hq hp1.le (N.cylOf A)).symm
  have h3 : (subBox N.dom N.ide N.hdom).fkMeasure hq hp1.le
        (subBox N.dom N.ide N.hdom).freeBoundary (N.cylOf A)
      ≤ C.graph.fkMeasure hq hp1.le α
          {ω : C.graph.Configuration | restrictI N.ide ω ∈ N.cylOf A} :=
    fkMeasure_cyl_ge_free (G := C.graph) (dom := N.dom) (I := N.ide) (hdom := N.hdom)
      (α := α) (q := q) (p := p) hq1 hp0 hp1 (N.cylOf_isUpperSet hA)
  exact h1.trans_le (h2.trans_le h3)

end NestedBox

end FK.NestedMixture

#print axioms FK.NestedMixture.NestedBox.nested_free_mass_le
#print axioms FK.NestedMixture.NestedBox.subBox_fkMeasure_eq_transport
#print axioms FK.NestedMixture.NestedBox.nested_mass_le_of_any_boundary
