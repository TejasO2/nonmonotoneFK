import FK.AGTree.Spine
import FK.AGTree.ThresholdExamples

/-!
# Quasi-transitive device geometry on the two-class tree

Combining vertex transitivity (`Ultra/Transitive.lean`), exact degree five
(`Ultra/Degree.lean`) and the explicit double ray (`Ultra/Spine.lean`), the
existing quasi-transitive device-packing theorem
`FK.QuasiTransitive.exists_separated_star_devices` produces genuine separated,
bounded-distance star devices on the two-class tree.  These are the geometric
inputs of the enhancement/AG packing argument (Theorem 1.4 / Proposition 4.2),
here instantiated on a concrete graph rather than assumed.

The tree has no cycles, so the cycle-device variant
`FK.QuasiTransitive.exists_separated_cycle_devices` is vacuous for it; only the
star side of the geometric sandwich is available on this graph.

Finally `two_class_reference_model` records the *previously proved* threshold
facts (`FK.AGTree.BaseNonpercolation`, `FK.AGTree.SharpThreshold`,
`FK.AGTree.ShiftThreshold`) together with the new geometry, so that the whole
model is stated on one quasi-transitive bounded-degree graph.  The threshold
content of that statement is not new; only the geometry and the device
existence are.
-/

namespace Ultra

open V
open scoped ENNReal NNReal unitInterval

/-- The pivot edge at the root of the two-class tree: the root's `spineA`-edge. -/
def rootPivot : G.edgeSet := childE ⟨(V.root, spineA), (by left; rfl)⟩

lemma root_mem_rootPivot : V.root ∈ (rootPivot : Sym2 V) := by
  rw [rootPivot]
  show V.root ∈ s(V.root, V.root.snoc spineA (by left; rfl))
  rw [Sym2.mem_iff]
  exact Or.inl rfl

lemma onDoubleRay_rootPivot : FK.EssentialEnhancement.OnDoubleRay rootPivot :=
  onDoubleRay_rootEdge

/-- **Separated star devices on the two-class tree.**  There is a set `S` of
pivots, dense at bounded line-graph distance, carrying finite star devices of at
most five edges, each an actual incidence star at a vertex of its pivot, and
pairwise separated in the sense of `FKLimit.IsSeparatedDeviceFamily`. -/
theorem exists_separated_star_devices :
    ∃ (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, FK.EssentialEnhancement.OnDoubleRay e) ∧
      (∀ e ∈ S, (D e).card ≤ 5) ∧
      (∀ e ∈ S, ∃ v : V, D e = FK.QuasiTransitive.starDevice G v ∧ v ∈ (e : Sym2 V)) := by
  obtain ⟨Delta, S, D, -, hsep, hbdd, hray, -, hwit⟩ :=
    FK.QuasiTransitive.exists_separated_star_devices G G_connected isQuasiTransitive
      V.root root_mem_rootPivot onDoubleRay_rootPivot
  refine ⟨S, D, hsep, hbdd, hray, ?_, hwit⟩
  intro e he
  obtain ⟨v, hD, -⟩ := hwit e he
  rw [hD, FK.QuasiTransitive.card_starDevice, degree_eq_five v]

/-- The uniform degree bound requested by the packing interface, with the exact
value five. -/
theorem exists_degree_bound_five :
    ∃ Delta : ℕ, (∀ v, G.degree v ≤ Delta) ∧ Delta = 5 :=
  ⟨5, degree_le_five, rfl⟩

/-- **The two-class reference model on one quasi-transitive graph.**  The
reduced-word tree is connected, locally finite, quasi-transitive (one orbit) and
regular of degree five; the two-rate independent bond law has a genuine strict
activation phase transition, and the graph carries separated star devices of
size at most five.

The threshold conjuncts are the previously proved statements of
`FK.AGTree.SharpThreshold`/`FK.AGTree.ShiftThreshold`; the geometry conjuncts are
proved in this development. -/
theorem two_class_reference_model :
    G.Connected ∧
    FK.QuasiTransitive.IsQuasiTransitive G ∧
    (∀ v : V, G.degree v = 5) ∧
    (pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} = 0) ∧
    (0 < pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω}) ∧
    (∃ (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, (D e).card ≤ 5)) := by
  refine ⟨G_connected, isQuasiTransitive, degree_eq_five, base_nonpercolation,
    activated_percolation, ?_⟩
  obtain ⟨S, D, hsep, hbdd, -, hcard, -⟩ := exists_separated_star_devices
  exact ⟨S, D, hsep, hbdd, hcard⟩

end Ultra
