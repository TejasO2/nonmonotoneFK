import FK.ClosedBoundary

/-!
# Eventual containment in a closed-boundary exhaustion

The free-specification step of Theorem 5.1 of arXiv:2512.16486 applies to a
fixed cylindrical event, hence to a fixed finite vertex set.  These lemmas
make precise why every such set is eventually contained in a monotone
closed-boundary exhaustion.
-/

open Filter Set

namespace FK
namespace ClosedBoundaryExhaustion

variable {V : Type*} {G H : SimpleGraph V}
  (E : ClosedBoundaryExhaustion G H)

/-- Every vertex eventually belongs to the exhaustion regions. -/
lemma eventually_mem (x : V) : ∀ᶠ n in atTop, x ∈ E.region n := by
  have hx : x ∈ ⋃ n, E.region n := by
    rw [E.exhaustive]
    exact Set.mem_univ x
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
  filter_upwards [eventually_ge_atTop N] with n hn
  exact E.monotone hn hN

/-- Every finite vertex set is eventually contained in a single region.  This
is the deterministic input for eventual equality of cylinder conditionals. -/
lemma eventually_subset {T : Set V} (hT : T.Finite) :
    ∀ᶠ n in atTop, T ⊆ E.region n := by
  have h : ∀ᶠ n in atTop, ∀ x ∈ hT.toFinset, x ∈ E.region n := by
    rw [Finset.eventually_all]
    exact fun x _hx ↦ E.eventually_mem x
  filter_upwards [h] with n hn
  intro x hx
  exact hn x (hT.mem_toFinset.mpr hx)

/-- Package eventual finite containment as an existential statement, with all
finite, connected, and closed-boundary properties retained. -/
lemma exists_region_superset {T : Set V} (hT : T.Finite) :
    ∃ n, T ⊆ E.region n ∧ (E.region n).Finite ∧
      (G.induce (E.region n)).Connected ∧ ClosedBoundary G H (E.region n) := by
  obtain ⟨n, hn⟩ := (E.eventually_subset hT).exists
  exact ⟨n, hn, E.finite n, E.connected n, E.closed n⟩

end ClosedBoundaryExhaustion
end FK
