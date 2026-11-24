import FK.GeometricActiveComparisons
import FK.FKWeakLimitActiveDevices

/-!
# Proposition 4.2 in the source's own FK-measure scope

The paper (arXiv:2512.16486v1, Proposition 4.2 and its proof on pp. 20–21)
fixes an infinite, connected, locally finite graph `G`, an exhaustion `Λ_n ↑ G`
and two sets of enhanced edges:

* `Ê ⊆ E` such that every `e ∈ Ê` lies in a star-device whose other edges are
  outside `Ê`;
* `Ẽ ⊆ E` such that every `e ∈ Ẽ` lies in a cycle-device of a fixed length `L`
  whose other edges are outside `Ẽ`.

With `ε̂ = |p' - p| (1 - max(p,p'))^{Δ-1}` and `ε̃ = |p' - p| min(p,p')^{L-1}`
it concludes, for *every* FK measure `φ` (that is: every weak limit along `Λ_n`
with partitions `α_n ∈ Π(∂Λ_n)`, and every DLR/Gibbs measure for any
convention),

`ℙ_{p + ε̂ 1_Ê} ⪯ φ ⪯ ℙ_{p' - ε̃ 1_Ẽ}` when `p < p'`, and the mirrored
statement when `p' < p`.

This module closes that statement on the labelled-box model of this project.
The two structural facts of the source that are *not* consequences of
measurability alone, and that this file therefore keeps as exact hypotheses,
are:

1. `SourceBoundaryClasses`: the finite-box boundary partition of the source is
   a partition of `∂Λ` only, so a vertex whose whole global incidence star is
   inside the box has a singleton class.  In the paper this is automatic
   (`Φ_Λ : {0,1}^{E(Λ)^c} → Π(∂Λ)`); the labelled-box model allows partitions
   of all box vertices, hence the hypothesis.  `hasSourceBoundaryClass_ofBoundaryPartition`
   below shows that every partition of the boundary set gives an instance, so
   the hypothesis is exactly the source's `Π(∂Λ)` and not a strengthening.
2. The device data of Definition 4.1 (whole star at a vertex, whole cycle of
   length `L`), separated from the enhanced set, with uniform cardinality
   bounds `Δ` and `L`.

Everything else — the finite closed-cutset / open-path comparisons of
Propositions 3.1 and 3.2, the cylinder transport to weak limits, the DLR
transport, the `ε̂`/`ε̃` arithmetic and the passage from activated finite
sub-families to the full enhanced sets — is proved in the imported public
modules and is only instantiated here.

The result is a comparison theorem for `φ` (the content used in the proof of
Theorem 1.4); the Aizenman–Grimmett strict critical shift is *not* asserted.

The constants are faithful: `FK.starEpsilon p q Δ = |p'−p|(1−max(p,p'))^{Δ−1}`
and `FK.cycleEpsilon p q L = |p'−p| min(p,p')^{L−1}` with
`p' = FK.fkSingletonParameter p q`.  `Δ` and `L` are used only as upper bounds
for the device cardinalities (`L` also fixes the selected cycle length), so any
such bound is valid and the source's sharp values are the least ones (maximal
degree, shortest pivotal cycle).

Note also that in the source's proof of Theorem 1.4 the sentence pairing
`ε̂` with `Ẽ` and `ε̃` with `Ê` is swapped: Proposition 4.2(1) gives
`φ ⪯ ℙ_{p'−ε̃1_Ẽ}` for `p < p'` and item (2) gives `φ ⪯ ℙ_{p−ε̂1_Ê}` for
`p > p'`.  `proposition_4_2_lt`/`_gt` below expose both conjuncts, so the
correct pairing is the one to use.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology

namespace FK.Prop42Source

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FKLimit

noncomputable section

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

/-! ## The source boundary condition `α_n ∈ Π(∂Λ_n)` -/

/-- Vertices of a labelled box that lie on the source's boundary `∂Λ`: those
with a globally incident edge leaving the box.  (`StarContained` is the
negation: every global edge incident to the vertex is a box edge.) -/
def boundaryVertices (data : SimpleGraphBoxData G box) (n : ℕ) : Set (box n).Vertex :=
  {c | ¬ data.StarContained n c}

/-- The finite-box boundary condition of the source: only boundary vertices may
be identified; every vertex with a box-contained incidence star has a singleton
class.  This is the labelled-box rendering of `α_n ∈ Π(∂Λ_n)`. -/
def HasSourceBoundaryClass (data : SimpleGraphBoxData G box) {n : ℕ}
    (ξ : (box n).BoundaryPartition) : Prop :=
  ∀ c : (box n).Vertex, data.StarContained n c →
    (box n).graph.HasSingletonBoundaryClass ξ c

/-- A sequence of source boundary conditions, one for each box of the
exhaustion. -/
def SourceBoundaryClasses (data : SimpleGraphBoxData G box)
    (ξ : ∀ n, (box n).BoundaryPartition) : Prop :=
  ∀ n, HasSourceBoundaryClass data (ξ n)

/-- A convention whose finite-box partitions are partitions of the boundary
only, for every exterior configuration. -/
def SourceConvention (data : SimpleGraphBoxData G box)
    (Φ : FK.InfiniteVolume.BoundaryAssignment box) : Prop :=
  ∀ (n : ℕ) (η : (box n).Exterior), HasSourceBoundaryClass data (Φ.partition n η)

/-- The quotient map attaching a label to each box vertex: boundary vertices
are labelled by their `s`-class, interior vertices by themselves. -/
def boundaryClassMap (data : SimpleGraphBoxData G box) (n : ℕ)
    (s : Setoid {c : (box n).Vertex // c ∈ boundaryVertices data n}) (c : (box n).Vertex) :
    Quotient s ⊕ (box n).Vertex :=
  if h : c ∈ boundaryVertices data n then Sum.inl (Quotient.mk s ⟨c, h⟩) else Sum.inr c

set_option warn.classDefReducibility false in
/-- Every partition of the boundary set extends to a box partition in which all
interior vertices are singletons.  This is the inclusion `Π(∂Λ_n) ↪` box
partitions, and shows that `HasSourceBoundaryClass` is satisfiable and is
exactly the source's model. -/
def ofBoundaryPartition (data : SimpleGraphBoxData G box) (n : ℕ)
    (s : Setoid {c : (box n).Vertex // c ∈ boundaryVertices data n}) :
    (box n).BoundaryPartition :=
  Setoid.ker (boundaryClassMap data n s)

/-- The extension of a boundary partition is a source boundary condition: an
interior vertex is labelled by itself, so its class is a singleton. -/
lemma hasSourceBoundaryClass_ofBoundaryPartition (data : SimpleGraphBoxData G box)
    (n : ℕ) (s : Setoid {c : (box n).Vertex // c ∈ boundaryVertices data n}) :
    HasSourceBoundaryClass data (ofBoundaryPartition data n s) := by
  intro c hc u hcu
  have hc' : ¬ c ∈ boundaryVertices data n := by
    simpa only [boundaryVertices, Set.mem_ofPred_eq, not_not] using hc
  have hmap_c : boundaryClassMap data n s c = Sum.inr c := by
    simp only [boundaryClassMap, hc', dite_false]
  have hku : boundaryClassMap data n s c = boundaryClassMap data n s u := hcu
  rw [hmap_c] at hku
  by_cases hu : u ∈ boundaryVertices data n
  · have hmap_u : boundaryClassMap data n s u = Sum.inl (Quotient.mk s ⟨u, hu⟩) := by
      simp only [boundaryClassMap, hu, dite_true]
    rw [hmap_u] at hku
    exact absurd hku (by simp)
  · have hmap_u : boundaryClassMap data n s u = Sum.inr u := by
      simp only [boundaryClassMap, hu, dite_false]
    rw [hmap_u] at hku
    exact (Sum.inr.inj hku).symm

/-- A geometrically valid convention is a source convention: a box-contained
star center has a singleton exterior component, so every geometric partition
keeps it a singleton class.  The source boundary hypothesis is therefore
weaker than, and implied by, the `IsGeometric` hypothesis of
`FK.EnhancedTransport.lt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained`. -/
lemma sourceConvention_of_isGeometric (data : SimpleGraphBoxData G box) [Countable V]
    {Φ : FK.InfiniteVolume.BoundaryAssignment box}
    (hΦ : IsGeometric data.geometry Φ) (hinj : ∀ n, Function.Injective (data.vertex n)) :
    SourceConvention data Φ :=
  fun n η c hc => data.hasSingletonBoundaryClass_of_isGeometric Φ hΦ n c hc (hinj n) η

/-! ## Star cutsets for source boundary conditions -/

/-- Containment of the whole star device in the box makes its center a
non-boundary vertex: every global edge at the center is a box edge.  This is
the finite manifestation of "the endpoints are not both in `∂Λ_n`" in the
source proof. -/
lemma starContained_of_starDevice_subset (data : SimpleGraphBoxData G box)
    [G.LocallyFinite] {n : ℕ} {c : (box n).Vertex} {D : Finset G.edgeSet}
    (hD : D = starDevice G (data.vertex n c)) (hsub : D ⊆ (box n).edges) :
    data.StarContained n c := by
  intro f hf
  have hfs : f ∈ starDevice G (data.vertex n c) := (mem_starDevice G).mpr hf
  rw [← hD] at hfs
  exact hsub hfs

/-- The erased incidence star at the device center is a closed cutset for the
finite-box connection event, for any boundary partition that gives every
box-contained center a singleton class.  This is the finite step of the source
proof: "if all the edges except `e` of the star-device are closed, it yields a
closed cutset for `e`". -/
theorem exists_starCutset_of_source_boundary (data : SimpleGraphBoxData G box)
    [G.LocallyFinite] {S : Set G.edgeSet} {D : G.edgeSet → Finset G.edgeSet}
    (hsep : IsSeparatedDeviceFamily S D)
    (hstar : ∀ f ∈ S, ∃ v : V, D f = starDevice G v ∧ v ∈ (f : Sym2 V))
    {Delta : ℕ} (hcard : ∀ f ∈ S, (D f).card ≤ Delta)
    {n : ℕ} {ξ : (box n).BoundaryPartition} (hξ : HasSourceBoundaryClass data ξ)
    {e : (box n).edges} (heS : (e : G.edgeSet) ∈ S)
    (hsub : D (e : G.edgeSet) ⊆ (box n).edges)
    (enhanced : Set (box n).edges) (henh : ∀ a ∈ enhanced, (a : G.edgeSet) ∈ S) :
    ∃ χ : Finset (box n).edges,
      ((χ : Finset (box n).edges) : Set (box n).edges) ∈
        CutsetFamily (graphConnectionEvent (box n).graph ξ) enhanced e ∧
      χ.card ≤ Delta - 1 := by
  obtain ⟨v, hD, hv⟩ := hstar (e : G.edgeSet) heS
  refine data.exists_starCutset_of_global_star hsep hv hD hsub heS enhanced henh ξ
    (fun c hvc hc => hξ c ?_) (hcard (e : G.edgeSet) heS)
  rw [← hvc] at hD
  exact starContained_of_starDevice_subset data hD hsub

end

end FK.Prop42Source

namespace FK.Prop42Source

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FKLimit

noncomputable section

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

set_option warn.classDefReducibility false in
/-! ## The `q < 1` comparison for every source DLR measure -/

/-- **Proposition 4.2(1) for Gibbs measures.**  For `q < 1` (so `p < p'`), every
DLR measure of a convention whose finite-box partitions are partitions of `∂Λ`
satisfies the two enhanced-product bounds, with the source's `ε̂` on the star set
and `ε̃` on the cycle set.  The only geometric input is the actual star/cycle
device data; `IsGeometric` is not assumed. -/
theorem lt_dlr_sandwich_of_source_convention
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box) (hΦ : SourceConvention data Φ)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : (p : ℝ) < fkSingletonParameter (p : ℝ) (q : ℝ) :=
      (self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
    StochasticallyDominates
      (bernoulliProduct (ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  dsimp only
  have hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpp : (p : ℝ) < fkSingletonParameter (p : ℝ) (q : ℝ) :=
    (self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
  constructor
  · apply lt_dlr_lower_of_active_star_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Sstar Dstar (ContainedAdmissible exh Dstar) Delta hStar
      (fun e _ => eventually_containedAdmissible exh Dstar e) hne
    intro n η e he
    exact exists_starCutset_of_source_boundary data hStar hstar hstarCard (hΦ n η)
      (mem_activeEdges.mp he).2.1 (mem_activeEdges.mp he).2.2.1 _
      (fun a ha => (mem_activeEdges.mp (mem_activeWithinFinset.mp ha)).2.1)
  · exact lt_dlr_upper_of_active_cyclePathFamily exh data Φ hinj hq hp0 hp1 hq1
      hp hqR hpp hμ Scycle Dcycle (ContainedAdmissible exh Dcycle) L hCycle
      (fun e _ => eventually_containedAdmissible exh Dcycle e) hcycle hcycleCard hne

set_option warn.classDefReducibility false in
/-! ## The `q > 1` comparison for every source DLR measure -/

/-- **Proposition 4.2(2) for Gibbs measures.**  The `q > 1` companion of
`lt_dlr_sandwich_of_source_convention`: the lower product is enhanced on the
cycle set and the upper product is lowered on the star set. -/
theorem gt_dlr_sandwich_of_source_convention
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box) (hΦ : SourceConvention data Φ)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ (lt_trans zero_lt_one hq1) hp1.le)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hq : 0 < q := lt_trans zero_lt_one hq1
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) ∧
    StochasticallyDominates
      (bernoulliProduct (gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ := by
  dsimp only
  let hq : 0 < q := lt_trans zero_lt_one hq1
  have hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpp : fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
    (fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
  constructor
  · exact gt_dlr_lower_of_active_cyclePathFamily exh data Φ hinj hq hp0 hp1 hq1
      hp hqR hpp hμ Scycle Dcycle (ContainedAdmissible exh Dcycle) L hCycle
      (fun e _ => eventually_containedAdmissible exh Dcycle e) hcycle hcycleCard hne
  · apply gt_dlr_upper_of_active_star_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Sstar Dstar (ContainedAdmissible exh Dstar) Delta hStar
      (fun e _ => eventually_containedAdmissible exh Dstar e) hne
    intro n η e he
    exact exists_starCutset_of_source_boundary data hStar hstar hstarCard (hΦ n η)
      (mem_activeEdges.mp he).2.1 (mem_activeEdges.mp he).2.2.1 _
      (fun a ha => (mem_activeEdges.mp (mem_activeWithinFinset.mp ha)).2.1)

end

end FK.Prop42Source

namespace FK.Prop42Source

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FKLimit

noncomputable section

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

/-! ## The comparison for every FK weak limit along the exhaustion -/

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(1) for limit measures.**  For `q < 1`, every weak limit
of finite-volume FK laws along the exhaustion with source boundary conditions
`α_n ∈ Π(∂Λ_n)` satisfies the enhanced-product bounds.  Compared with
`FK.EnhancedTransport.lt_fkLimit_sandwich_of_active_devices_interior`, the
star cutset and cycle path certificates are no longer inputs: they are
produced from the actual star/cycle devices of Definition 4.1. -/
theorem lt_fkLimit_sandwich_of_source_devices
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box)
    (α : ∀ n, (exh.box n).BoundaryPartition) (hα : SourceBoundaryClasses data α)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : IsFKLimit exh hq hp1.le α μ)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : (p : ℝ) < fkSingletonParameter (p : ℝ) (q : ℝ) :=
      (self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
    StochasticallyDominates
      (bernoulliProduct (ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  dsimp only
  classical
  let Γ : ∀ n, (exh.box n).edges → Set (Finset (exh.box n).edges) :=
    fun n e => cyclePathFamily (exh.box n) Dcycle e
  refine lt_fkLimit_sandwich_of_active_devices_interior exh α hq hp0 hp1 hq1 hμ
    Sstar Dstar (ContainedAdmissible exh Dstar) Delta hStar
    (fun e _ => eventually_containedAdmissible exh Dstar e) hne ?_
    Scycle Dcycle (ContainedAdmissible exh Dcycle) L hCycle
    (fun e _ => eventually_containedAdmissible exh Dcycle e) Γ ?_ ?_ ?_
  · -- star cutset certificate from the actual star devices
    intro n e he
    exact exists_starCutset_of_source_boundary data hStar hstar hstarCard (hα n)
      (mem_activeEdges.mp he).2.1 (mem_activeEdges.mp he).2.2.1 _
      (fun a ha => (mem_activeEdges.mp (mem_activeWithinFinset.mp ha)).2.1)
  · -- the complementary cycle support is an auxiliary path family
    intro n e he
    exact cyclePathFamily_auxiliaryPaths (exh.box n)
      (activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle (ContainedAdmissible exh Dcycle) n)
      Scycle Dcycle hCycle (fun a ha => activeEdges_subset ha)
      (mem_activeEdges.mp (mem_activeWithinFinset.mp he)).2.1
  · -- opening the complementary cycle support proves the connection event
    intro n e he ω hω
    obtain ⟨γ, hγ, hopen⟩ := hω
    have hγeq : γ = (activeWithinFinset (exh.box n) (Dcycle (e : G.edgeSet))).erase e := by
      simpa only [Γ, cyclePathFamily, Set.mem_singleton_iff] using hγ
    subst hγeq
    have he' := FKLimit.mem_activeEdges.mp (mem_activeWithinFinset.mp he)
    obtain ⟨v, c, hc, -, hDcycle, heC⟩ := hcycle (e : G.edgeSet) he'.2.1
    exact data.graphConnectionEvent_of_cyclePathOpen n (hinj n) (α n) e (Dcycle (e : G.edgeSet))
      he'.2.2.1 c hc hDcycle heC hopen
  · -- one member of the cycle path family with the uniform predecessor bound
    intro n e he
    have he' := FKLimit.mem_activeEdges.mp he
    exact exists_cyclePathFamily_card_le (exh.box n) Dcycle e L
      (hCycle (e : G.edgeSet) he'.2.1).1 (hcycleCard (e : G.edgeSet) he'.2.1)

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(2) for limit measures**, the `q > 1` companion of
`lt_fkLimit_sandwich_of_source_devices`. -/
theorem gt_fkLimit_sandwich_of_source_devices
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box)
    (α : ∀ n, (exh.box n).BoundaryPartition) (hα : SourceBoundaryClasses data α)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : IsFKLimit exh (lt_trans zero_lt_one hq1) hp1.le α μ)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hq : 0 < q := lt_trans zero_lt_one hq1
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) ∧
    StochasticallyDominates
      (bernoulliProduct (gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ := by
  dsimp only
  classical
  let hq : 0 < q := lt_trans zero_lt_one hq1
  let Γ : ∀ n, (exh.box n).edges → Set (Finset (exh.box n).edges) :=
    fun n e => cyclePathFamily (exh.box n) Dcycle e
  refine gt_fkLimit_sandwich_of_active_devices_interior exh α hp0 hp1 hq1 hμ
    Sstar Dstar (ContainedAdmissible exh Dstar) Delta hStar
    (fun e _ => eventually_containedAdmissible exh Dstar e) hne ?_
    Scycle Dcycle (ContainedAdmissible exh Dcycle) L hCycle
    (fun e _ => eventually_containedAdmissible exh Dcycle e) Γ ?_ ?_ ?_
  · intro n e he
    exact exists_starCutset_of_source_boundary data hStar hstar hstarCard (hα n)
      (mem_activeEdges.mp he).2.1 (mem_activeEdges.mp he).2.2.1 _
      (fun a ha => (mem_activeEdges.mp (mem_activeWithinFinset.mp ha)).2.1)
  · intro n e he
    exact cyclePathFamily_auxiliaryPaths (exh.box n)
      (activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle (ContainedAdmissible exh Dcycle) n)
      Scycle Dcycle hCycle (fun a ha => activeEdges_subset ha)
      (mem_activeEdges.mp (mem_activeWithinFinset.mp he)).2.1
  · intro n e he ω hω
    obtain ⟨γ, hγ, hopen⟩ := hω
    have hγeq : γ = (activeWithinFinset (exh.box n) (Dcycle (e : G.edgeSet))).erase e := by
      simpa only [Γ, cyclePathFamily, Set.mem_singleton_iff] using hγ
    subst hγeq
    have he' := FKLimit.mem_activeEdges.mp (mem_activeWithinFinset.mp he)
    obtain ⟨v, c, hc, -, hDcycle, heC⟩ := hcycle (e : G.edgeSet) he'.2.1
    exact data.graphConnectionEvent_of_cyclePathOpen n (hinj n) (α n) e (Dcycle (e : G.edgeSet))
      he'.2.2.1 c hc hDcycle heC hopen
  · intro n e he
    have he' := FKLimit.mem_activeEdges.mp he
    exact exists_cyclePathFamily_card_le (exh.box n) Dcycle e L
      (hCycle (e : G.edgeSet) he'.2.1).1 (hcycleCard (e : G.edgeSet) he'.2.1)

end

end FK.Prop42Source

namespace FK.Prop42Source

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FKLimit

noncomputable section

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

/-! ## The paper's `ε̂` and `ε̃` in the two enhanced products -/

/-- The lower product of Proposition 4.2(1) is `p + ε̂` on `Ê` and `p`
elsewhere, exactly as in the source. -/
lemma ltLowerParameters_apply {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : p < FKLimit.fkSingletonParameter p q) (Delta : ℕ) (Sstar : Set E) (e : E) :
    (FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar e : ℝ) =
      if e ∈ Sstar then p + FKLimit.starEpsilon p q Delta else p := by
  simp only [FKLimit.ltLowerParameters, FKLimit.unitParameters, FKLimit.raisedOn]

/-- The upper product of Proposition 4.2(1) is `p' - ε̃` on `Ẽ` and `p'`
elsewhere, exactly as in the source. -/
lemma ltUpperParameters_apply {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : p < FKLimit.fkSingletonParameter p q) (L : ℕ) (Scycle : Set E) (e : E) :
    (FKLimit.ltUpperParameters p q hp hq hpp L Scycle e : ℝ) =
      if e ∈ Scycle then FKLimit.fkSingletonParameter p q - FKLimit.cycleEpsilon p q L
      else FKLimit.fkSingletonParameter p q := by
  simp only [FKLimit.ltUpperParameters, FKLimit.unitParameters, FKLimit.loweredOn]

/-- The lower product of Proposition 4.2(2) is `p' + ε̃` on `Ẽ` and `p'`
elsewhere. -/
lemma gtLowerParameters_apply {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : FKLimit.fkSingletonParameter p q < p) (L : ℕ) (Scycle : Set E) (e : E) :
    (FKLimit.gtLowerParameters p q hp hq hpp L Scycle e : ℝ) =
      if e ∈ Scycle then FKLimit.fkSingletonParameter p q + FKLimit.cycleEpsilon p q L
      else FKLimit.fkSingletonParameter p q := by
  simp only [FKLimit.gtLowerParameters, FKLimit.unitParameters, FKLimit.raisedOn]

/-- The upper product of Proposition 4.2(2) is `p - ε̂` on `Ê` and `p`
elsewhere. -/
lemma gtUpperParameters_apply {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : FKLimit.fkSingletonParameter p q < p) (Delta : ℕ) (Sstar : Set E) (e : E) :
    (FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar e : ℝ) =
      if e ∈ Sstar then p - FKLimit.starEpsilon p q Delta else p := by
  simp only [FKLimit.gtUpperParameters, FKLimit.unitParameters, FKLimit.loweredOn]

/-! ## The FK-measure class of the source -/

/-- The class of measures that Proposition 4.2 quantifies over, in the project
model: weak limits of finite-volume FK laws along the exhaustion with source
boundary conditions `α_n ∈ Π(∂Λ_n)`, together with DLR laws of measurable
conventions whose finite-box partitions are partitions of `∂Λ`. -/
def SourceFKMeasure [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)) : Prop :=
  (∃ α : ∀ n, (exh.box n).BoundaryPartition,
      SourceBoundaryClasses data α ∧ IsFKLimit exh hq hp α μ) ∨
    (∃ Φ : FK.InfiniteVolume.BoundaryAssignment exh.box,
      SourceConvention data Φ ∧ μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp)

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(1)** in the source's FK-measure scope: for `q < 1` every
FK measure of the source class is sandwiched between the star-enhanced and the
cycle-enhanced Bernoulli products. -/
theorem proposition_4_2_lt
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : SourceFKMeasure exh data hq hp1.le μ)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : (p : ℝ) < fkSingletonParameter (p : ℝ) (q : ℝ) :=
      (self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
    StochasticallyDominates
      (bernoulliProduct (ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  rcases hμ with ⟨α, hα, hμ⟩ | ⟨Φ, hΦ, hμ⟩
  · exact lt_fkLimit_sandwich_of_source_devices exh data α hα hinj hq hp0 hp1 hq1 hμ
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne
  · exact lt_dlr_sandwich_of_source_convention exh data Φ hΦ hinj hq hp0 hp1 hq1 hμ
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(2)** in the source's FK-measure scope: for `q > 1` every
FK measure of the source class is sandwiched between the cycle-enhanced and the
star-lowered Bernoulli products. -/
theorem proposition_4_2_gt
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : SourceFKMeasure exh data (lt_trans zero_lt_one hq1) hp1.le μ)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    let hq : 0 < q := lt_trans zero_lt_one hq1
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) ∧
    StochasticallyDominates
      (bernoulliProduct (gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ := by
  rcases hμ with ⟨α, hα, hμ⟩ | ⟨Φ, hΦ, hμ⟩
  · exact gt_fkLimit_sandwich_of_source_devices exh data α hα hinj hp0 hp1 hq1 hμ
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne
  · exact gt_dlr_sandwich_of_source_convention exh data Φ hΦ hinj hp0 hp1 hq1 hμ
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne

end

end FK.Prop42Source

namespace FK.Prop42Source

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FKLimit

noncomputable section

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

/-! ## Which conventions are source conventions -/

/-- The free convention of the paper (`Φ^f`: nothing happens at infinity) is a
source convention: a box-contained star center has a singleton exterior open
component. -/
theorem sourceConvention_free (data : SimpleGraphBoxData G box) [Countable V]
    (hinj : ∀ n, Function.Injective (data.vertex n)) :
    SourceConvention data data.free := by
  intro n η c hc
  exact data.free_hasSingletonBoundaryClass n c hc (hinj n) η

/-- The wired-at-infinity convention of the paper (`Φ^w`: all infinite exterior
clusters merged) is a source convention: a box-contained star center is never in
an infinite exterior cluster, so it cannot be merged with anything. -/
theorem sourceConvention_wired (data : SimpleGraphBoxData G box) [Countable V]
    (hinj : ∀ n, Function.Injective (data.vertex n)) :
    SourceConvention data data.wired := by
  intro n η c hc
  exact data.wired_hasSingletonBoundaryClass n c hc (hinj n) η

/-- Every geometric DLR class (the hypothesis of
`FK.EnhancedTransport.lt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained`)
is contained in the source FK-measure class of Proposition 4.2. -/
theorem sourceFKMeasure_of_geometric_dlr [Countable V] [Countable G.edgeSet]
    {exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet}
    (data : SimpleGraphBoxData G exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    {Φ : FK.InfiniteVolume.BoundaryAssignment exh.box}
    (hΦ : IsGeometric data.geometry Φ)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp) :
    SourceFKMeasure exh data hq hp μ :=
  Or.inr ⟨Φ, sourceConvention_of_isGeometric data hΦ hinj, hμ⟩

/-- Free-convention DLR laws belong to the source FK-measure class. -/
theorem sourceFKMeasure_of_dlr_free [Countable V] [Countable G.edgeSet]
    {exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet}
    (data : SimpleGraphBoxData G exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh data.free hq hp) :
    SourceFKMeasure exh data hq hp μ :=
  Or.inr ⟨data.free, sourceConvention_free data hinj, hμ⟩

/-- Wired-at-infinity DLR laws belong to the source FK-measure class. -/
theorem sourceFKMeasure_of_dlr_wired [Countable V] [Countable G.edgeSet]
    {exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet}
    (data : SimpleGraphBoxData G exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh data.wired hq hp) :
    SourceFKMeasure exh data hq hp μ :=
  Or.inr ⟨data.wired, sourceConvention_wired data hinj, hμ⟩

end

end FK.Prop42Source

#print axioms FK.Prop42Source.hasSourceBoundaryClass_ofBoundaryPartition
#print axioms FK.Prop42Source.starContained_of_starDevice_subset
#print axioms FK.Prop42Source.exists_starCutset_of_source_boundary
#print axioms FK.Prop42Source.lt_dlr_sandwich_of_source_convention
#print axioms FK.Prop42Source.gt_dlr_sandwich_of_source_convention
#print axioms FK.Prop42Source.lt_fkLimit_sandwich_of_source_devices
#print axioms FK.Prop42Source.gt_fkLimit_sandwich_of_source_devices
#print axioms FK.Prop42Source.proposition_4_2_lt
#print axioms FK.Prop42Source.proposition_4_2_gt
#print axioms FK.Prop42Source.sourceConvention_free
#print axioms FK.Prop42Source.sourceConvention_wired
#print axioms FK.Prop42Source.sourceFKMeasure_of_geometric_dlr
#print axioms FK.Prop42Source.sourceFKMeasure_of_dlr_free
#print axioms FK.Prop42Source.sourceFKMeasure_of_dlr_wired

namespace FK.Prop42Source

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FKLimit

noncomputable section

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(1) for the graph class of Theorem 1.4.**  On a connected
quasi-transitive graph with a pivotal edge lying on a cycle, the source's
generic device construction produces the separated star/cycle families and the
uniform `Δ`, `L`, and every source FK measure satisfies the resulting
enhanced-product bounds for `q < 1`.  No device data is an input. -/
theorem proposition_4_2_lt_of_quasiTransitive
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    (hconn : G.Connected) (hqt : FK.QuasiTransitive.IsQuasiTransitive G)
    {u₀ : V} {e₀ : G.edgeSet} (hu₀ : u₀ ∈ (e₀ : Sym2 V))
    (hr₀ : FK.EssentialEnhancement.OnDoubleRay e₀)
    {v₀ : V} (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle) (he₀ : (e₀ : Sym2 V) ∈ c₀.edges)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : SourceFKMeasure exh data hq hp1.le μ)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    ∃ (Delta L : ℕ) (Sstar Scycle : Set G.edgeSet)
      (Dstar Dcycle : G.edgeSet → Finset G.edgeSet),
      IsSeparatedDeviceFamily Sstar Dstar ∧
      IsSeparatedDeviceFamily Scycle Dcycle ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Sstar ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Scycle ∧
      (∀ f ∈ Sstar, (Dstar f).card ≤ Delta) ∧
      (∀ f ∈ Scycle, (Dcycle f).card ≤ L) ∧
      (∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V)) ∧
      (∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
        Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges) ∧
      (let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
       let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
       let hpp : (p : ℝ) < fkSingletonParameter (p : ℝ) (q : ℝ) :=
         (self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
       StochasticallyDominates μ
         (bernoulliProduct (ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
       StochasticallyDominates
         (bernoulliProduct (ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ) := by
  obtain ⟨Delta, Sstar, Dstar, -, hStar, hstarBounded, -, hstarCard, hstar⟩ :=
    FK.QuasiTransitive.exists_separated_star_devices G hconn hqt u₀ hu₀ hr₀
  obtain ⟨L, Scycle, Dcycle, -, hCycle, hcycleBounded, -, hcycleCard, hcycle⟩ :=
    FK.QuasiTransitive.exists_separated_cycle_devices G hconn hqt c₀ hc₀ he₀ hr₀
  exact ⟨Delta, L, Sstar, Scycle, Dstar, Dcycle, hStar, hCycle, hstarBounded,
    hcycleBounded, hstarCard, hcycleCard, hstar, hcycle,
    proposition_4_2_lt exh data hinj hq hp0 hp1 hq1 hμ Sstar Dstar Delta hStar hstar
      hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne⟩

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(2) for the graph class of Theorem 1.4**, the `q > 1`
companion of `proposition_4_2_lt_of_quasiTransitive`. -/
theorem proposition_4_2_gt_of_quasiTransitive
    [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : SimpleGraphBoxData G exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    (hconn : G.Connected) (hqt : FK.QuasiTransitive.IsQuasiTransitive G)
    {u₀ : V} {e₀ : G.edgeSet} (hu₀ : u₀ ∈ (e₀ : Sym2 V))
    (hr₀ : FK.EssentialEnhancement.OnDoubleRay e₀)
    {v₀ : V} (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle) (he₀ : (e₀ : Sym2 V) ∈ c₀.edges)
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : SourceFKMeasure exh data (lt_trans zero_lt_one hq1) hp1.le μ)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    ∃ (Delta L : ℕ) (Sstar Scycle : Set G.edgeSet)
      (Dstar Dcycle : G.edgeSet → Finset G.edgeSet),
      IsSeparatedDeviceFamily Sstar Dstar ∧
      IsSeparatedDeviceFamily Scycle Dcycle ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Sstar ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist Scycle ∧
      (∀ f ∈ Sstar, (Dstar f).card ≤ Delta) ∧
      (∀ f ∈ Scycle, (Dcycle f).card ≤ L) ∧
      (∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V)) ∧
      (∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
        Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges) ∧
      (let hq : 0 < q := lt_trans zero_lt_one hq1
       let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
       let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
       let hpp : fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
         (fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
       StochasticallyDominates μ
         (bernoulliProduct (gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) ∧
       StochasticallyDominates
         (bernoulliProduct (gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ) := by
  obtain ⟨Delta, Sstar, Dstar, -, hStar, hstarBounded, -, hstarCard, hstar⟩ :=
    FK.QuasiTransitive.exists_separated_star_devices G hconn hqt u₀ hu₀ hr₀
  obtain ⟨L, Scycle, Dcycle, -, hCycle, hcycleBounded, -, hcycleCard, hcycle⟩ :=
    FK.QuasiTransitive.exists_separated_cycle_devices G hconn hqt c₀ hc₀ he₀ hr₀
  exact ⟨Delta, L, Sstar, Scycle, Dstar, Dcycle, hStar, hCycle, hstarBounded,
    hcycleBounded, hstarCard, hcycleCard, hstar, hcycle,
    proposition_4_2_gt exh data hinj hp0 hp1 hq1 hμ Sstar Dstar Delta hStar hstar
      hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne⟩

end

end FK.Prop42Source

#print axioms FK.Prop42Source.proposition_4_2_lt_of_quasiTransitive
#print axioms FK.Prop42Source.proposition_4_2_gt_of_quasiTransitive

namespace FK.Prop42Source

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FKLimit

noncomputable section

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

/-! ## The exhaustion-free form: every FK measure of the source class -/

universe w

/-- The source's class of FK measures, with the exhaustion existentially
quantified as in the paper ("there exists an increasing sequence `Λ_n ↑ G`
and `α_n ∈ Π(∂Λ_n)` with `φ = lim φ^{α_n}_{Λ_n,p,q}`"), together with the
DLR/Gibbs measures of source conventions.  No exhaustion is fixed. -/
def IsSourceFKMeasure {V : Type u} {G : SimpleGraph V} [Countable G.edgeSet]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)) : Prop :=
  (∃ (exh : FK.InfiniteVolume.BoxExhaustion.{u, w} G.edgeSet)
      (data : SimpleGraphBoxData G exh.box)
      (α : ∀ n, (exh.box n).BoundaryPartition),
      (∀ n, Function.Injective (data.vertex n)) ∧
      (∀ n, Nonempty (exh.box n).edges) ∧
      SourceBoundaryClasses data α ∧ IsFKLimit exh hq hp α μ) ∨
    (∃ (exh : FK.InfiniteVolume.BoxExhaustion.{u, w} G.edgeSet)
      (data : SimpleGraphBoxData G exh.box)
      (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box),
      (∀ n, Function.Injective (data.vertex n)) ∧
      (∀ n, Nonempty (exh.box n).edges) ∧
      SourceConvention data Φ ∧ μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp)

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(1), exhaustion-free form.**  For `q < 1` every FK limit
measure along some genuine exhaustion with partitions of `∂Λ_n`, and every
Gibbs measure of a convention with partitions of `∂Λ_n`, satisfies the
star/cycle enhanced comparison. -/
theorem proposition_4_2_lt_forall
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : IsSourceFKMeasure (G := G) hq hp1.le μ)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L) :
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : (p : ℝ) < fkSingletonParameter (p : ℝ) (q : ℝ) :=
      (self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
    StochasticallyDominates
      (bernoulliProduct (ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  rcases hμ with ⟨exh, data, α, hinj, hne, hα, hμ⟩ | ⟨exh, data, Φ, hinj, hne, hΦ, hμ⟩
  · exact proposition_4_2_lt exh data hinj hq hp0 hp1 hq1 (Or.inl ⟨α, hα, hμ⟩)
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne
  · exact proposition_4_2_lt exh data hinj hq hp0 hp1 hq1 (Or.inr ⟨Φ, hΦ, hμ⟩)
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne

set_option warn.classDefReducibility false in
/-- **Proposition 4.2(2), exhaustion-free form.** -/
theorem proposition_4_2_gt_forall
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite] [Countable G.edgeSet]
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : IsSourceFKMeasure (G := G) (lt_trans zero_lt_one hq1) hp1.le μ)
    (Sstar : Set G.edgeSet) (Dstar : G.edgeSet → Finset G.edgeSet) (Delta : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hstar : ∀ f ∈ Sstar, ∃ v : V, Dstar f = starDevice G v ∧ v ∈ (f : Sym2 V))
    (hstarCard : ∀ f ∈ Sstar, (Dstar f).card ≤ Delta)
    (Scycle : Set G.edgeSet) (Dcycle : G.edgeSet → Finset G.edgeSet) (L : ℕ)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycle : ∀ f ∈ Scycle, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      Dcycle f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcycleCard : ∀ f ∈ Scycle, (Dcycle f).card ≤ L) :
    let hq : 0 < q := lt_trans zero_lt_one hq1
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
    StochasticallyDominates μ
      (bernoulliProduct (gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) ∧
    StochasticallyDominates
      (bernoulliProduct (gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ := by
  rcases hμ with ⟨exh, data, α, hinj, hne, hα, hμ⟩ | ⟨exh, data, Φ, hinj, hne, hΦ, hμ⟩
  · exact proposition_4_2_gt exh data hinj hp0 hp1 hq1 (Or.inl ⟨α, hα, hμ⟩)
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne
  · exact proposition_4_2_gt exh data hinj hp0 hp1 hq1 (Or.inr ⟨Φ, hΦ, hμ⟩)
      Sstar Dstar Delta hStar hstar hstarCard Scycle Dcycle L hCycle hcycle hcycleCard hne

end

end FK.Prop42Source

#print axioms FK.Prop42Source.proposition_4_2_lt_forall
#print axioms FK.Prop42Source.proposition_4_2_gt_forall
