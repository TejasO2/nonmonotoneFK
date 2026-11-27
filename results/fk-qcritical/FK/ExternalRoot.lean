import FK.IncidenceAttachment

open scoped Classical
open CurvatureVariance.Infra.Percolation
open Set

namespace FK.BurtonKeane
open FK.ClusterCover

universe u
variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- Incidence to a finite vertex set is finite. -/
lemma finite_incidence [G.LocallyFinite] {U : Set V} (hU : U.Finite) :
    (incidence G U).Finite := by
  apply (hU.biUnion fun x _ => (G.incidenceSet x).toFinite).subset
  intro e he
  obtain ⟨heG, x, hxU, hxe⟩ := he
  exact Set.mem_biUnion hxU ⟨heG, hxe⟩

/-- Restrict a cover to representatives belonging to its original full open
component, without losing coverage. -/
lemma exists_finite_cover_in_cluster (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    (r : V) (A : Set (Sym2 V)) (hA : A.Finite) :
    ∃ L : Set V, L.Finite ∧ (∀ z ∈ L, OpenConnected G ω Set.univ z r) ∧
      ∀ y ∈ clusterAvoid G ω ∅ r, ∃ z ∈ L, y ∈ clusterAvoid G ω A z := by
  obtain ⟨L, hLfin, hcover⟩ := exists_finite_cover (G := G) (ω := ω) r hA
  let L' := {z ∈ L | OpenConnected G ω Set.univ z r}
  refine ⟨L', hLfin.subset (fun z hz => hz.1), fun z hz => hz.2, ?_⟩
  intro y hy
  obtain ⟨z, hzL, hz⟩ := hcover y hy
  have hz_y : OpenConnected G ω Set.univ z y := hz.mono_edges (Set.subset_univ _)
  have hy_r : OpenConnected G ω Set.univ y r := by
    obtain ⟨p, hp⟩ := hy
    exact ⟨p.reverse, (isOpenIn_reverse p hp).mono_edges (Set.subset_univ _)⟩
  exact ⟨z, ⟨hzL, hz_y.trans hy_r⟩, hz⟩

/-- Select an outside infinite incident-avoiding component while retaining
its original full open link to the original cluster root. -/
theorem exists_external_root [G.LocallyFinite] {U : Set V} (hU : U.Finite)
    {r : V} (hinf : {z | OpenConnected G ω Set.univ r z}.Infinite) :
    ∃ z ∉ U, (clusterAvoid G ω (incidence G U) z).Infinite ∧
      ∃ p : G.Walk r z, IsOpenIn ω Set.univ p := by
  let A := incidence G U
  obtain ⟨L, hLfin, hlinks, hcover⟩ := @exists_finite_cover_in_cluster V G ω
    r (incidence G U) (finite_incidence hU)
  have hBig : (⋃ z ∈ L, clusterAvoid G ω A z).Infinite := by
    apply hinf.mono
    intro y hy
    have hy' : y∈clusterAvoid G ω ∅ r := by
      simpa [clusterAvoid_empty_eq] using hy
    obtain ⟨z, hzL, hz⟩ := hcover y hy'
    exact Set.mem_iUnion₂.mpr ⟨z, hzL, hz⟩
  have hzExists : ∃ z ∈ L, (clusterAvoid G ω A z).Infinite := by
    by_contra hn
    push_neg at hn
    exact hBig (hLfin.biUnion hn)
  obtain ⟨z, hzL, hinfz⟩ := hzExists
  have hzr : OpenConnected G ω Set.univ z r := hlinks z hzL
  obtain ⟨p, hp⟩ := hzr
  refine ⟨z, not_mem_of_infinite_clusterAvoid_incidence hU hinfz, hinfz,
    p.reverse, (isOpenIn_reverse p hp).mono_edges (Set.subset_univ _)⟩


/-- An original full open connection to an external root transports every
outside-root nonconnection into an incident-avoiding nonconnection. -/
lemma external_nonConnected_of_nonConnected {U : Set V} {r z : V}
    (p : G.Walk r z) (hp : IsOpenIn ω Set.univ p) {s : V}
    (hs : ¬ OpenConnected G ω Set.univ r s) :
    ¬ OpenConnected G ω (Set.univ \ incidence G U) z s := by
  intro hzs
  obtain ⟨q, hq⟩ := hzs
  apply hs
  exact ⟨p.append q, isOpenIn_append.mpr ⟨hp, hq.mono_edges (Set.subset_univ _)⟩⟩
