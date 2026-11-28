import FK.SourceUniqueness
import FK.QOneLine
import FK.EncounterProbability
import FK.FolnerFirstMoment
import FK.ClusterTail
import FK.GlobalOuterGeometry
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Automorphism invariance at the actual source-FK interface

At `q = 1`, every law in either summand of `SourceFKMeasures` is the constant
Bernoulli product.  Consequently every such law, including an arbitrary source
weak limit, is invariant under every graph automorphism.  No invariance of the
boundary convention is assumed.  The general `q ≠ 1` assertion is not made.

The file also develops the deterministic transport of open connection and
three-arm geometry needed for centre-local homogeneous marked events.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal unitInterval Classical Topology
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane.Automorphism

open FK.InfiniteVolume FK.InfiniteVolume.ConventionTransport FK.InfiniteVolume.ConventionGeometry FK.SourceUniqueness FK.SourceRegions

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-- Move a configuration forward along a graph automorphism. -/
def permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) : G.edgeSet → Bool :=
  fun e => ω (φ.symm.mapEdgeSet e)

/-- The coordinate-permutation equivalence agrees with `permConfig`. -/
lemma piCongrLeft_eq_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) :
    (MeasurableEquiv.piCongrLeft (fun _ => Bool) φ.mapEdgeSet) ω = permConfig φ ω := by
  funext e
  have h := Equiv.piCongrLeft_apply_apply (fun _ => Bool) φ.mapEdgeSet ω
    (φ.mapEdgeSet.symm e)
  rw [Equiv.apply_symm_apply] at h
  rw [MeasurableEquiv.coe_piCongrLeft, h, SimpleGraph.Iso.mapEdgeSet_symm_apply]
  rfl

@[simp] lemma permConfig_symm_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) :
    permConfig φ.symm (permConfig φ ω) = ω := by
  funext e
  exact congrArg ω (φ.mapEdgeSet.symm_apply_apply e)

@[simp] lemma permConfig_permConfig_symm (φ : G ≃g G) (ω : G.edgeSet → Bool) :
    permConfig φ (permConfig φ.symm ω) = ω := by
  funext e
  exact congrArg ω (φ.mapEdgeSet.apply_symm_apply e)

/-- A constant-rate independent Boolean product is invariant under every
coordinate equivalence. -/
theorem measurePreserving_piCongrLeft_percolation (p : unitInterval) (φ : G ≃g G) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ => Bool) φ.mapEdgeSet)
      (percolation G p) (percolation G p) := by
  refine ⟨MeasurableEquiv.measurable _, ?_⟩
  exact Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : G.edgeSet => bernoulliMeasure true false p)
    (X := fun _ => Bool) φ.mapEdgeSet

/-- Function-level form of automorphism invariance for Bernoulli percolation. -/
theorem measurePreserving_permConfig_percolation (p : unitInterval) (φ : G ≃g G) :
    MeasurePreserving (permConfig φ) (percolation G p) (percolation G p) := by
  have h := measurePreserving_piCongrLeft_percolation (G := G) p φ
  have heq : (MeasurableEquiv.piCongrLeft (fun _ => Bool) φ.mapEdgeSet :
      (G.edgeSet → Bool) → (G.edgeSet → Bool)) = permConfig φ := by
    funext ω
    exact piCongrLeft_eq_permConfig φ ω
  rw [heq] at h
  exact h

/-- The `q = 1` source measure is automorphism invariant. -/
theorem measurePreserving_permConfig_bernoulliConst [Countable V]
    (p : NNReal) (hp : p ≤ 1) (φ : G ≃g G) :
    MeasurePreserving (permConfig (G := G) φ)
      (FK.InfiniteVolume.QOne.bernoulliConst (E := G.edgeSet) p hp :
        Measure (Configuration G.edgeSet))
      (FK.InfiniteVolume.QOne.bernoulliConst (E := G.edgeSet) p hp :
        Measure (Configuration G.edgeSet)) := by
  exact measurePreserving_permConfig_percolation (G := G)
    (FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp) φ

/-- Both summands of the actual source family collapse to the same Bernoulli
product at `q = 1`.  The supplied vertex exhaustion is used only to restrict an
all-region source-DLR convention to an ordinary DLR class. -/
theorem eq_bernoulliConst_of_mem_sourceFKMeasures_q_one [Countable V]
    [G.LocallyFinite] (E : VertexExhaustion V) {p : NNReal} (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) zero_lt_one hp) :
    μ = FK.InfiniteVolume.QOne.bernoulliConst (E := G.edgeSet) p hp := by
  rcases hμ with hdlr | hweak
  · obtain ⟨Φ, hΦ⟩ := Set.mem_iUnion.mp hdlr
    exact FK.InfiniteVolume.QOne.eq_bernoulliConst_of_mem_dlrMeasures_q_one
      (E.exhaustion (G := G)) (assignment E Φ) hp
      ((mem_sourceDLR_iff_mem_dlr_restrict E Φ μ).1 hΦ.2)
  · obtain ⟨F, α, _hα, hlim⟩ := hweak
    exact FK.InfiniteVolume.QOne.eq_bernoulliConst_of_isFKLimit_q_one
      (F.exhaustion (G := G)) hp α hlim

/-- **Actual source-law invariance at `q = 1`.**  This applies to source weak
limits as well as all-region geometric source-DLR laws; the convention itself
need not be automorphism invariant. -/
theorem measurePreserving_permConfig_of_mem_sourceFKMeasures_q_one
    [Countable V] [G.LocallyFinite] (E : VertexExhaustion V)
    {p : NNReal} (hp : p ≤ 1) (φ : G ≃g G)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) zero_lt_one hp) :
    MeasurePreserving (permConfig φ) (μ : Measure (Configuration G.edgeSet))
      (μ : Measure (Configuration G.edgeSet)) := by
  rw [eq_bernoulliConst_of_mem_sourceFKMeasures_q_one E hp hμ]
  exact measurePreserving_permConfig_bernoulliConst p hp φ

/-! ### Transport of open walks -/

/-- The actual edge corresponding to an adjacency proof. -/
def edgeOf {x y : V} (h : G.Adj x y) : G.edgeSet := ⟨s(x, y), h⟩

lemma edgeOf_mapEdgeSet {φ : G ≃g G} {x y : V} (h : G.Adj x y) :
    φ.mapEdgeSet (edgeOf h) = edgeOf (φ.toHom.map_adj h) := by
  apply Subtype.ext
  rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
  rfl

/-- Openness is preserved by mapping a walk forward along an automorphism. -/
lemma isOpenIn_map_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool)
    {x y : V} (w : G.Walk x y) (hw : IsOpenIn ω Set.univ w) :
    IsOpenIn (permConfig φ ω) Set.univ (w.map φ.toHom) := by
  induction w with
  | nil => exact isOpenIn_nil
  | @cons x y z hxy w ih =>
    rw [SimpleGraph.Walk.map_cons, isOpenIn_cons]
    rw [isOpenIn_cons] at hw
    refine ⟨⟨Set.mem_univ _, ?_⟩, ih hw.2⟩
    have hsame : edgeOf (φ.symm.toHom.map_adj (φ.toHom.map_adj hxy)) = edgeOf hxy := by
      apply Subtype.ext
      simp
    change (permConfig φ ω) (edgeOf (φ.toHom.map_adj hxy)) = true
    rw [permConfig, edgeOf_mapEdgeSet (φ := φ.symm) (φ.toHom.map_adj hxy), hsame]
    exact hw.1.2

/-- Forward transport of open connection. -/
theorem openConnected_map_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool)
    {x y : V} (h : OpenConnected G ω Set.univ x y) :
    OpenConnected G (permConfig φ ω) Set.univ (φ x) (φ y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.map φ.toHom, isOpenIn_map_permConfig φ ω w hw⟩

/-- Open connection is exactly equivariant under automorphisms. -/
theorem openConnected_permConfig_iff (φ : G ≃g G) (ω : G.edgeSet → Bool)
    (x y : V) :
    OpenConnected G (permConfig φ ω) Set.univ (φ x) (φ y) ↔
      OpenConnected G ω Set.univ x y := by
  refine ⟨fun h => ?_, openConnected_map_permConfig φ ω⟩
  have h' := openConnected_map_permConfig φ.symm (permConfig φ ω) h
  simpa using h'

/-- The open cluster at `φ x` is the image of the open cluster at `x`. -/
theorem clusterSet_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) (x : V) :
    {z | OpenConnected G (permConfig φ ω) Set.univ (φ x) z} =
      φ '' {z | OpenConnected G ω Set.univ x z} := by
  ext z
  constructor
  · intro hz
    refine ⟨φ.symm z, ?_, by simp⟩
    have h := (openConnected_permConfig_iff φ ω x (φ.symm z)).1 (by simpa using hz)
    simpa using h
  · rintro ⟨y, hy, rfl⟩
    exact (openConnected_permConfig_iff φ ω x y).2 hy

/-- Infinitude of a rooted open cluster is automorphism equivariant. -/
theorem infiniteClusterAt_permConfig_iff (φ : G ≃g G) (ω : G.edgeSet → Bool) (x : V) :
    {z | OpenConnected G (permConfig φ ω) Set.univ (φ x) z}.Infinite ↔
      {z | OpenConnected G ω Set.univ x z}.Infinite := by
  rw [clusterSet_permConfig]
  exact Set.infinite_image_iff (fun _a _ _b _ h => φ.injective h)

/-- The three-separated-infinite-clusters event is globally invariant. -/
theorem threeInfiniteClusters_permConfig_iff (φ : G ≃g G) (ω : G.edgeSet → Bool) :
    ThreeInfiniteClusters G (permConfig φ ω) ↔ ThreeInfiniteClusters G ω := by
  constructor
  · intro h
    have h' : ThreeInfiniteClusters G (permConfig φ.symm (permConfig φ ω)) := by
      obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := h
      refine ⟨φ.symm a, φ.symm b, φ.symm c, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hh := (infiniteClusterAt_permConfig_iff φ.symm (permConfig φ ω) a).2 (by simpa using ha)
        simpa using hh
      · have hh := (infiniteClusterAt_permConfig_iff φ.symm (permConfig φ ω) b).2 (by simpa using hb)
        simpa using hh
      · have hh := (infiniteClusterAt_permConfig_iff φ.symm (permConfig φ ω) c).2 (by simpa using hc)
        simpa using hh
      · intro hc'
        have hc0 : OpenConnected G ω Set.univ (φ.symm a) (φ.symm b) := by simpa using hc'
        exact hab (by simpa using openConnected_map_permConfig φ ω hc0)
      · intro hc'
        have hc0 : OpenConnected G ω Set.univ (φ.symm a) (φ.symm c) := by simpa using hc'
        exact hac (by simpa using openConnected_map_permConfig φ ω hc0)
      · intro hc'
        have hc0 : OpenConnected G ω Set.univ (φ.symm b) (φ.symm c) := by simpa using hc'
        exact hbc (by simpa using openConnected_map_permConfig φ ω hc0)
    simpa using h'
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
    refine ⟨φ a, φ b, φ c, (infiniteClusterAt_permConfig_iff φ ω a).2 ha,
      (infiniteClusterAt_permConfig_iff φ ω b).2 hb,
      (infiniteClusterAt_permConfig_iff φ ω c).2 hc, ?_, ?_, ?_⟩
    · exact fun h => hab ((openConnected_permConfig_iff φ ω a b).1 h)
    · exact fun h => hac ((openConnected_permConfig_iff φ ω a c).1 h)
    · exact fun h => hbc ((openConnected_permConfig_iff φ ω b c).1 h)


/-! ### Transport of three-arm geometry and finite internal openings -/

/-- Graph automorphisms preserve metric distance on a connected graph. -/
theorem dist_iso (hG : G.Connected) (φ : G ≃g G) (x y : V) :
    G.dist (φ x) (φ y) = G.dist x y := by
  apply le_antisymm
  · obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist x y
    rw [← hw, ← SimpleGraph.Walk.length_map]
    exact SimpleGraph.dist_le (w.map φ.toHom)
  · obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist (φ x) (φ y)
    have hle := SimpleGraph.dist_le (w.map φ.symm.toHom)
    simp only [SimpleGraph.Walk.length_map] at hle
    rw [hw] at hle
    simpa using hle

/-- Map a three-arm witness forward, preserving openness, simplicity,
separation and the exact metric scale. -/
theorem threeWayArms_map_permConfig (hG : G.Connected) (φ : G ≃g G)
    (ω : G.edgeSet → Bool) {y : V} {n : ℕ} (h : ThreeWayArms G ω y n) :
    ThreeWayArms G (permConfig φ ω) (φ y) n := by
  obtain ⟨a, b, c, pa, pb, pc, hna, hnb, hnc, hpa, hpb, hpc,
    hoa, hob, hoc, hab, hac, hbc⟩ := h
  refine ⟨φ a, φ b, φ c, pa.map φ.toHom, pb.map φ.toHom, pc.map φ.toHom,
    ?_, ?_, ?_, hpa.map φ.injective, hpb.map φ.injective, hpc.map φ.injective,
    isOpenIn_map_permConfig φ ω pa hoa, isOpenIn_map_permConfig φ ω pb hob,
    isOpenIn_map_permConfig φ ω pc hoc, ?_, ?_, ?_⟩
  · simpa only [dist_iso hG] using hna
  · simpa only [dist_iso hG] using hnb
  · simpa only [dist_iso hG] using hnc
  · intro z hza hzb
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hza hzb
    obtain ⟨za, hza, rfl⟩ := hza
    obtain ⟨zb, hzb, heq⟩ := hzb
    have hz : zb = za := φ.injective heq
    subst zb
    exact congrArg φ (hab za hza hzb)
  · intro z hza hzc
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hza hzc
    obtain ⟨za, hza, rfl⟩ := hza
    obtain ⟨zc, hzc, heq⟩ := hzc
    have hz : zc = za := φ.injective heq
    subst zc
    exact congrArg φ (hac za hza hzc)
  · intro z hzb hzc
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hzb hzc
    obtain ⟨zb, hzb, rfl⟩ := hzb
    obtain ⟨zc, hzc, heq⟩ := hzc
    have hz : zc = zb := φ.injective heq
    subst zc
    exact congrArg φ (hbc zb hzb hzc)

/-- Three-way arms at a centre are exactly automorphism equivariant. -/
theorem threeWayArms_permConfig_iff (hG : G.Connected) (φ : G ≃g G)
    (ω : G.edgeSet → Bool) (y : V) (n : ℕ) :
    ThreeWayArms G (permConfig φ ω) (φ y) n ↔ ThreeWayArms G ω y n := by
  refine ⟨fun h => ?_, threeWayArms_map_permConfig hG φ ω⟩
  have h' := threeWayArms_map_permConfig hG φ.symm (permConfig φ ω) h
  simpa using h'

/-- Membership of a mapped edge in the internal-edge set of a mapped vertex
set. -/
lemma mem_internal_mapEdgeSet_iff (φ : G ≃g G) (U : Set V) (e : G.edgeSet) :
    ((φ.mapEdgeSet e : G.edgeSet) : Sym2 V) ∈ internal G (φ '' U) ↔
      (e : Sym2 V) ∈ internal G U := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [internal, Set.mem_ofPred_eq, FK.QuasiTransitive.iso_coe_mapEdgeSet,
      Sym2.map_mk, SimpleGraph.mem_edgeSet, Sym2.forall_mem_pair]
    simp only [φ.map_adj_iff, Set.mem_image]
    constructor
    · rintro ⟨hab, ⟨x, hx, hax⟩, ⟨y, hy, hby⟩⟩
      exact ⟨hab, φ.injective hax ▸ hx, φ.injective hby ▸ hy⟩
    · rintro ⟨hab, ha, hb⟩
      exact ⟨hab, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩

/-- Finite internal opening commutes with automorphism transport. -/
theorem openInternal_image_permConfig (φ : G ≃g G) (U : Set V) (ω : G.edgeSet → Bool) :
    openInternal (φ '' U) (permConfig φ ω) = permConfig φ (openInternal U ω) := by
  funext e
  let e₀ : G.edgeSet := φ.mapEdgeSet.symm e
  have he : φ.mapEdgeSet e₀ = e := φ.mapEdgeSet.apply_symm_apply e
  rw [← he]
  by_cases h : (e₀ : Sym2 V) ∈ internal G U
  · have h' : ((φ.mapEdgeSet e₀ : G.edgeSet) : Sym2 V) ∈ internal G (φ '' U) :=
      (mem_internal_mapEdgeSet_iff φ U e₀).2 h
    rw [openInternal_of_mem _ h']
    have hval : permConfig φ (openInternal U ω) (φ.mapEdgeSet e₀) =
        openInternal U ω e₀ := by
      change openInternal U ω (φ.symm.mapEdgeSet (φ.mapEdgeSet e₀)) =
        openInternal U ω e₀
      have he₀ : φ.symm.mapEdgeSet (φ.mapEdgeSet e₀) = e₀ :=
        φ.mapEdgeSet.symm_apply_apply e₀
      rw [he₀]
    rw [hval, openInternal_of_mem _ h]
  · have h' : ((φ.mapEdgeSet e₀ : G.edgeSet) : Sym2 V) ∉ internal G (φ '' U) :=
      fun hn => h ((mem_internal_mapEdgeSet_iff φ U e₀).1 hn)
    rw [openInternal_of_notMem _ h']
    have hval : permConfig φ (openInternal U ω) (φ.mapEdgeSet e₀) =
        openInternal U ω e₀ := by
      change openInternal U ω (φ.symm.mapEdgeSet (φ.mapEdgeSet e₀)) =
        openInternal U ω e₀
      have he₀ : φ.symm.mapEdgeSet (φ.mapEdgeSet e₀) = e₀ :=
        φ.mapEdgeSet.symm_apply_apply e₀
      rw [he₀]
    have hvalω : permConfig φ ω (φ.mapEdgeSet e₀) = ω e₀ := by
      change ω (φ.symm.mapEdgeSet (φ.mapEdgeSet e₀)) = ω e₀
      have he₀ : φ.symm.mapEdgeSet (φ.mapEdgeSet e₀) = e₀ :=
        φ.mapEdgeSet.symm_apply_apply e₀
      rw [he₀]
    rw [hval, hvalω, openInternal_of_notMem _ h]


/-! ### Centre-local patched encounters and the Følner interface -/

/-- A centre at which some finite internal opening leaves three-way arms at
all scales.  Existentially quantifying the patch is what makes this event
centre-local and automorphism equivariant. -/
def PatchedEncounterAt (G : SimpleGraph V) (y : V) : Set (G.edgeSet → Bool) :=
  {ω | ∃ U : Set V, U.Finite ∧ ∀ n : ℕ, ThreeWayArms G (openInternal U ω) y n}

/-- The global encounter event is the countable union of its centre-local
versions. -/
theorem encounterEvent_eq_iUnion_patchedEncounterAt (G : SimpleGraph V) :
    EncounterEvent G = ⋃ y : V, PatchedEncounterAt G y := by
  ext ω
  constructor
  · rintro ⟨U, hU, y, hy⟩
    exact Set.mem_iUnion.mpr ⟨y, U, hU, hy⟩
  · intro h
    obtain ⟨y, U, hU, hy⟩ := Set.mem_iUnion.mp h
    exact ⟨U, hU, y, hy⟩

/-- Centre-local patched encounters are measurable. -/
lemma measurableSet_patchedEncounterAt [Countable V] (y : V) :
    MeasurableSet (PatchedEncounterAt G y) := by
  have heq : PatchedEncounterAt G y =
      ⋃ U ∈ {U : Set V | U.Finite}, ⋂ n : ℕ,
        {η : G.edgeSet → Bool | ThreeWayArms G (openInternal U η) y n} := by
    ext η
    simp only [PatchedEncounterAt, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨U, hU, h⟩ <;> exact ⟨U, hU, h⟩
  rw [heq]
  exact MeasurableSet.biUnion Set.Countable.ofPred_finite fun U _ =>
    MeasurableSet.iInter fun n => by
      have hmeas : Measurable fun η : G.edgeSet → Bool => openInternal U η := by
        apply Measurable.of_eval
        intro e
        by_cases he : (e : Sym2 V) ∈ internal G U
        · simp only [openInternal, he, ite_true]
          exact measurable_const
        · simp only [openInternal, he, ite_false]
          exact measurable_pi_apply e
      exact (measurableSet_threeWayArms (G := G) y n).preimage hmeas

/-- Forward transport of centre-local patched encounters. -/
theorem patchedEncounterAt_map_permConfig (hG : G.Connected) (φ : G ≃g G)
    (ω : G.edgeSet → Bool) {y : V} (h : ω ∈ PatchedEncounterAt G y) :
    permConfig φ ω ∈ PatchedEncounterAt G (φ y) := by
  obtain ⟨U, hU, hy⟩ := h
  refine ⟨φ '' U, hU.image φ, fun n => ?_⟩
  have hmap := threeWayArms_map_permConfig hG φ (openInternal U ω) (hy n)
  rw [openInternal_image_permConfig]
  exact hmap

/-- Centre-local patched encounters are exactly automorphism equivariant. -/
theorem patchedEncounterAt_permConfig_iff (hG : G.Connected) (φ : G ≃g G)
    (ω : G.edgeSet → Bool) (y : V) :
    permConfig φ ω ∈ PatchedEncounterAt G (φ y) ↔ ω ∈ PatchedEncounterAt G y := by
  refine ⟨fun h => ?_, patchedEncounterAt_map_permConfig hG φ ω⟩
  have h' := patchedEncounterAt_map_permConfig hG φ.symm (permConfig φ ω) h
  simpa using h'

/-- Package actual measure/event invariance as the existing first-moment
`HomogeneousEvents` interface for centre-local patched encounters. -/
def homogeneousPatchedEncounterEvents [Countable V] (hG : G.Connected)
    {μ : Measure (G.edgeSet → Bool)}
    (hμ : ∀ φ : G ≃g G, MeasurePreserving (permConfig φ) μ μ)
    (root : V) (shift : V → G ≃g G) (hshift : ∀ v, shift v root = v) :
    Folner.HomogeneousEvents (G.edgeSet → Bool) V μ root where
  event := PatchedEncounterAt G
  shift v := permConfig (shift v)
  measurableSet_event := measurableSet_patchedEncounterAt
  measurePreserving_shift v := hμ (shift v)
  preimage_event v := by
    ext ω
    change permConfig (shift v) ω ∈ PatchedEncounterAt G v ↔
      ω ∈ PatchedEncounterAt G root
    have h := patchedEncounterAt_permConfig_iff hG (shift v) ω root
    rwa [hshift v] at h

/-- **Three-cluster exclusion from a genuine multi-centre Følner bound.**  The
bound is required for the centre-local patched event in every configuration,
not merely for one fixed-centre encounter tree. -/
theorem measure_threeInfiniteClusters_eq_zero_of_folner
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ]
    (hins : FinitePatternInsertionTolerance μ)
    (hinv : ∀ φ : G ≃g G, MeasurePreserving (permConfig φ) μ μ)
    (root : V) (shift : V → G ≃g G) (hshift : ∀ v, shift v root = v)
    (F : ℕ → Finset V) (b : ℕ → ℕ) (hF : ∀ n, (F n).Nonempty)
    (hbound : ∀ n ω, Folner.markedCount (PatchedEncounterAt G) (F n) ω ≤ b n)
    (hfolner : Tendsto (fun n => (b n : ℝ≥0∞) / (F n).card) atTop (𝓝 0)) :
    μ {ω | ThreeInfiniteClusters G ω} = 0 := by
  let H := homogeneousPatchedEncounterEvents hG hinv root shift hshift
  have hz : μ (H.event root) = 0 :=
    H.measure_root_eq_zero_of_folner F b hF (fun n ω => hbound n ω) hfolner
  by_contra hne
  have hS : 0 < μ {ω | ThreeInfiniteClusters G ω} := pos_iff_ne_zero.mpr hne
  have hEnc := measure_pos_encounterEvent_of_three_infinite_of_insertionTolerant
    hG μ hins hS
  rw [encounterEvent_eq_iUnion_patchedEncounterAt] at hEnc
  have hnull : μ (⋃ v : V, H.event v) = 0 := by
    apply measure_iUnion_null
    intro v
    rw [H.measure_event v, hz]
  exact (ne_of_gt hEnc) hnull

/-- Interior-rate `q = 1` specialization for an arbitrary member of the actual
source family.  Insertion tolerance comes from the Bernoulli product and
automorphism invariance from the source-family identification above. -/
theorem measure_threeInfiniteClusters_eq_zero_of_folner_q_one
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (X : VertexExhaustion V) {p : NNReal} (hp : p ≤ 1)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ SourceFKMeasures (G := G) zero_lt_one hp)
    (root : V) (shift : V → G ≃g G) (hshift : ∀ v, shift v root = v)
    (F : ℕ → Finset V) (b : ℕ → ℕ) (hF : ∀ n, (F n).Nonempty)
    (hbound : ∀ n ω, Folner.markedCount (PatchedEncounterAt G) (F n) ω ≤ b n)
    (hfolner : Tendsto (fun n => (b n : ℝ≥0∞) / (F n).card) atTop (𝓝 0)) :
    (μ : Measure (Configuration G.edgeSet)) {ω | ThreeInfiniteClusters G ω} = 0 := by
  have heq := eq_bernoulliConst_of_mem_sourceFKMeasures_q_one X hp hμ
  have hins : FinitePatternInsertionTolerance (μ : Measure (Configuration G.edgeSet)) := by
    rw [heq]
    exact finitePatternInsertionTolerance_bernoulliProduct
      (FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp)
      (by simpa [FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN] using hp0)
      (by simpa [FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN] using hp1)
  exact measure_threeInfiniteClusters_eq_zero_of_folner hG (μ : Measure _) hins
    (fun φ => measurePreserving_permConfig_of_mem_sourceFKMeasures_q_one X hp φ hμ)
    root shift hshift F b hF hbound hfolner


/-! ### The exactly-two-infinite-clusters case -/

/-- At least two distinguished infinite open clusters. -/
def TwoInfiniteClusters (G : SimpleGraph V) (ω : G.edgeSet → Bool) : Prop :=
  ∃ x y : V,
    {z | OpenConnected G ω Set.univ x z}.Infinite ∧
    {z | OpenConnected G ω Set.univ y z}.Infinite ∧
    ¬ OpenConnected G ω Set.univ x y

/-- Exactly two infinite open clusters, expressed by two separated infinite
clusters and the impossibility of a third separated one. -/
def ExactlyTwoInfiniteClusters (G : SimpleGraph V) (ω : G.edgeSet → Bool) : Prop :=
  TwoInfiniteClusters G ω ∧ ¬ ThreeInfiniteClusters G ω

/-- Every walk whose vertices lie in `U` is open after opening all internal
edges of `U`. -/
lemma isOpenIn_openInternal_of_support_subset {U : Set V} {x y : V}
    (w : G.Walk x y) (hw : ∀ z ∈ w.support, z ∈ U) (ω : G.edgeSet → Bool) :
    IsOpenIn (openInternal U ω) Set.univ w := by
  induction w with
  | nil => exact isOpenIn_nil
  | @cons x y z hxy w ih =>
    rw [isOpenIn_cons]
    refine ⟨⟨Set.mem_univ _, ?_⟩, ih (fun a ha => hw a (by simp [ha]))⟩
    apply openInternal_of_mem
    refine ⟨hxy, Sym2.forall_mem_pair.mpr ⟨?_, ?_⟩⟩
    · exact hw x (by simp)
    · exact hw y (by simp)

/-- A finite connected internal opening merges every configuration having
exactly two infinite clusters to a configuration with at most one. -/
theorem exists_openInternal_globalAtMostOne_of_exactlyTwo [G.LocallyFinite]
    (hG : G.Connected) {ω : G.edgeSet → Bool}
    (hω : ExactlyTwoInfiniteClusters G ω) :
    ∃ U : Set V, U.Finite ∧ GlobalAtMostOne G (openInternal U ω) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hω.1
  obtain ⟨U, hU, hxU, hyU, _hxU, hconn⟩ := exists_connected_support hG x y x
  refine ⟨U, hU, ?_⟩
  let η : G.edgeSet → Bool := openInternal U ω
  obtain ⟨wxy⟩ := hconn.preconnected ⟨x, hxU⟩ ⟨y, hyU⟩
  have hopen : ∀ {a b : U} (w : (G.induce U).Walk a b),
      IsOpenIn η Set.univ (w.map (SimpleGraph.Embedding.induce U).toHom) := by
    intro a b w
    induction w with
    | nil => exact isOpenIn_nil
    | @cons a b c hab q ih =>
      rw [SimpleGraph.Walk.map_cons, isOpenIn_cons]
      refine ⟨⟨Set.mem_univ _, ?_⟩, ih⟩
      apply openInternal_of_mem
      exact ⟨hab, Sym2.forall_mem_pair.mpr ⟨a.2, b.2⟩⟩
  have hxyη : OpenConnected G η Set.univ x y := ⟨_, hopen wxy⟩
  have hle : ω ≤ η := le_openInternal ω
  have htransport (z : V) : FK.ClusterCover.clusterAvoid G η (internal G U) z =
      FK.ClusterCover.clusterAvoid G ω (internal G U) z := by
    ext a
    change OpenConnected G η (Set.univ \ internal G U) z a ↔
      OpenConnected G ω (Set.univ \ internal G U) z a
    constructor
    · intro h
      exact OpenConnected.congr h fun e he => (openInternal_of_notMem e he.2)
    · intro h
      exact OpenConnected.congr h fun e he => (openInternal_of_notMem e he.2).symm
  have horiginal_infinite {z : V}
      (hz : (FK.ClusterCover.clusterAvoid G η (internal G U) z).Infinite) :
      {w | OpenConnected G ω Set.univ z w}.Infinite := by
    rw [htransport z] at hz
    rw [← FK.ClusterCover.clusterAvoid_empty_eq]
    exact hz.mono (FK.ClusterCover.clusterAvoid_antitone
      (Set.empty_subset (internal G U)) z)
  have hside (z : V) (hz : {w | OpenConnected G ω Set.univ z w}.Infinite) :
      OpenConnected G ω Set.univ x z ∨ OpenConnected G ω Set.univ y z := by
    by_contra hn
    push Not at hn
    exact hω.2 ⟨x, y, z, hx, hy, hz, hxy, hn.1, hn.2⟩
  intro a b ha hb
  change {z : V | OpenConnected G η Set.univ a z}.Infinite at ha
  change {z : V | OpenConnected G η Set.univ b z}.Infinite at hb
  have ha0 : (FK.ClusterCover.clusterAvoid G η ∅ a).Infinite := by
    simpa only [FK.ClusterCover.clusterAvoid_empty_eq] using ha
  have hb0 : (FK.ClusterCover.clusterAvoid G η ∅ b).Infinite := by
    simpa only [FK.ClusterCover.clusterAvoid_empty_eq] using hb
  have hA : (internal G U).Finite := by
    have hloc : ∀ e : Sym2 V, e ∈ internal G U → e ∈ incidence G U :=
      fun _ he => internal_subset_incidence G he
    exact (finite_incidence hU).subset hloc
  obtain ⟨za, haza, hza⟩ :=
    FK.NestedFinDLR.GlobalClosure.exists_infinite_cluster_avoid_connected hA ha0
  obtain ⟨zb, hazb, hzb⟩ :=
    FK.NestedFinDLR.GlobalClosure.exists_infinite_cluster_avoid_connected hA hb0
  have hzaω := horiginal_infinite hza
  have hzbω := horiginal_infinite hzb
  have hzaη : OpenConnected G η Set.univ za x ∨ OpenConnected G η Set.univ za y := by
    rcases hside za hzaω with h | h
    · exact Or.inl (OpenConnected.mono_config (openConnected_symm h) hle)
    · exact Or.inr (OpenConnected.mono_config (openConnected_symm h) hle)
  have hzbη : OpenConnected G η Set.univ zb x ∨ OpenConnected G η Set.univ zb y := by
    rcases hside zb hzbω with h | h
    · exact Or.inl (OpenConnected.mono_config (openConnected_symm h) hle)
    · exact Or.inr (OpenConnected.mono_config (openConnected_symm h) hle)
  have hzaX : OpenConnected G η Set.univ za x := by
    rcases hzaη with h | h
    · exact h
    · exact h.trans (openConnected_symm hxyη)
  have hzbX : OpenConnected G η Set.univ zb x := by
    rcases hzbη with h | h
    · exact h
    · exact h.trans (openConnected_symm hxyη)
  change OpenConnected G η Set.univ a b
  exact (haza.trans hzaX).trans (openConnected_symm (hazb.trans hzbX))

/-- Explicit finite-patch version of the deterministic exactly-two merge. -/
theorem exists_finitePatch_globalAtMostOne_of_exactlyTwo [G.LocallyFinite]
    (hG : G.Connected) {ω : G.edgeSet → Bool}
    (hω : ExactlyTwoInfiniteClusters G ω) :
    ∃ j : PatchIndex G.edgeSet,
      @Function.updateFinset G.edgeSet (fun _ => Bool)
        (fun a b => Classical.propDecidable (a = b)) ω j.1 j.2 ∈
          {η | GlobalAtMostOne G η} := by
  classical
  obtain ⟨U, hU, hmerge⟩ := exists_openInternal_globalAtMostOne_of_exactlyTwo hG hω
  refine ⟨⟨internalFinset (G := G) hU, fun _ => true⟩, ?_⟩
  dsimp only
  simp only [Set.mem_ofPred_eq]
  rw [← openInternal_eq_updateFinset (ω := ω) hU]
  exact hmerge

/-- **Finite insertion tolerance excludes an almost-sure exactly-two phase.**
This is the separate finite-count argument; it does not use or replace the
three-way encounter/Følner bound. -/
theorem not_ae_exactlyTwoInfiniteClusters_of_insertionTolerant
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ]
    (hins : FinitePatternInsertionTolerance μ) :
    ¬ (∀ᵐ ω ∂μ, ExactlyTwoInfiniteClusters G ω) := by
  intro hae
  have hcomp : μ {ω | ¬ ExactlyTwoInfiniteClusters G ω} = 0 := ae_iff.mp hae
  have hmass : μ {ω | ExactlyTwoInfiniteClusters G ω} = μ Set.univ :=
    measure_of_measure_compl_eq_zero hcomp
  have hS : 0 < μ {ω | ExactlyTwoInfiniteClusters G ω} := by
    rw [hmass]
    simp
  have hpos := measure_pos_of_forall_exists_patch_of_finitePatternInsertionTolerance
    μ hins (measurableSet_globalAtMostOne G) hS
    (fun ω hω => exists_finitePatch_globalAtMostOne_of_exactlyTwo hG hω)
  have hsub : {ω | GlobalAtMostOne G ω} ⊆
      {ω | ¬ ExactlyTwoInfiniteClusters G ω} := by
    intro ω huniq htwo
    obtain ⟨x, y, hx, hy, hxy⟩ := htwo.1
    exact hxy (huniq x y hx hy)
  have hzero : μ {ω | GlobalAtMostOne G ω} = 0 := measure_mono_null hsub hcomp
  exact (ne_of_gt hpos) hzero


/-- Measurability of a rooted infinite open cluster on any countable graph. -/
lemma measurableSet_rootedInfiniteCluster [Countable V] (x : V) :
    MeasurableSet {ω : G.edgeSet → Bool |
      {z | OpenConnected G ω Set.univ x z}.Infinite} := by
  exact MeasurableSet.setOfPred_infinite.preimage
    (FK.ClusterTail.measurable_openCluster G x)

/-- Measurability of at least two separated infinite clusters. -/
lemma measurableSet_twoInfiniteClusters [Countable V] :
    MeasurableSet {ω | TwoInfiniteClusters G ω} := by
  let infEvent : V → Set (G.edgeSet → Bool) := fun x =>
    {ω | {z | OpenConnected G ω Set.univ x z}.Infinite}
  let connEvent : V → V → Set (G.edgeSet → Bool) := fun x y =>
    {ω | OpenConnected G ω Set.univ x y}
  have hinfEvent : ∀ x : V, MeasurableSet (infEvent x) := fun x =>
    measurableSet_rootedInfiniteCluster (G := G) x
  have hconnEvent : ∀ x y : V, MeasurableSet (connEvent x y) := fun x y =>
    measurableSet_openConnected (G := G) Set.univ x y
  have heq : {ω | TwoInfiniteClusters G ω} =
      ⋃ x : V, ⋃ y : V, infEvent x ∩ infEvent y ∩ (connEvent x y)ᶜ := by
    ext ω
    simp only [TwoInfiniteClusters, infEvent, connEvent, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      exact ⟨x, y, ⟨hx, hy⟩, hxy⟩
    · rintro ⟨x, y, h⟩
      exact ⟨x, y, h.1.1, h.1.2, h.2⟩
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    ((hinfEvent x).inter (hinfEvent y)).inter (hconnEvent x y).compl

/-- Measurability of three separated infinite clusters. -/
lemma measurableSet_threeInfiniteClusters [Countable V] :
    MeasurableSet {ω | ThreeInfiniteClusters G ω} := by
  let infEvent : V → Set (G.edgeSet → Bool) := fun x =>
    {ω | {z | OpenConnected G ω Set.univ x z}.Infinite}
  let connEvent : V → V → Set (G.edgeSet → Bool) := fun x y =>
    {ω | OpenConnected G ω Set.univ x y}
  have hinfEvent : ∀ x : V, MeasurableSet (infEvent x) := fun x =>
    measurableSet_rootedInfiniteCluster (G := G) x
  have hconnEvent : ∀ x y : V, MeasurableSet (connEvent x y) := fun x y =>
    measurableSet_openConnected (G := G) Set.univ x y
  have heq : {ω | ThreeInfiniteClusters G ω} = ⋃ a : V, ⋃ b : V, ⋃ c : V,
      infEvent a ∩ infEvent b ∩ infEvent c ∩ (connEvent a b)ᶜ ∩ (connEvent a c)ᶜ ∩ (connEvent b c)ᶜ := by
    ext ω
    simp only [ThreeInfiniteClusters, infEvent, connEvent, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
      exact ⟨a, b, c, ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hac⟩, hbc⟩⟩
    · rintro ⟨a, b, c, h⟩
      exact ⟨a, b, c, h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2,
        h.1.1.2, h.1.2, h.2⟩
  rw [heq]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
    MeasurableSet.iUnion fun c =>
      (((((hinfEvent a).inter (hinfEvent b)).inter (hinfEvent c)).inter (hconnEvent a b).compl).inter
        (hconnEvent a c).compl).inter (hconnEvent b c).compl

/-- The exactly-two event is measurable. -/
lemma measurableSet_exactlyTwoInfiniteClusters [Countable V] :
    MeasurableSet {ω | ExactlyTwoInfiniteClusters G ω} := by
  exact measurableSet_twoInfiniteClusters.inter measurableSet_threeInfiniteClusters.compl

/-- Forward transport of at least two separated infinite clusters. -/
theorem twoInfiniteClusters_map_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool)
    (h : TwoInfiniteClusters G ω) : TwoInfiniteClusters G (permConfig φ ω) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨φ x, φ y, (infiniteClusterAt_permConfig_iff φ ω x).2 hx,
    (infiniteClusterAt_permConfig_iff φ ω y).2 hy, ?_⟩
  exact fun hc => hxy ((openConnected_permConfig_iff φ ω x y).1 hc)

/-- At least two separated infinite clusters is automorphism invariant. -/
theorem twoInfiniteClusters_permConfig_iff (φ : G ≃g G) (ω : G.edgeSet → Bool) :
    TwoInfiniteClusters G (permConfig φ ω) ↔ TwoInfiniteClusters G ω := by
  refine ⟨fun h => ?_, twoInfiniteClusters_map_permConfig φ ω⟩
  have h' := twoInfiniteClusters_map_permConfig φ.symm (permConfig φ ω) h
  simpa using h'

/-- The exactly-two event is automorphism invariant. -/
theorem exactlyTwoInfiniteClusters_permConfig_iff (φ : G ≃g G) (ω : G.edgeSet → Bool) :
    ExactlyTwoInfiniteClusters G (permConfig φ ω) ↔ ExactlyTwoInfiniteClusters G ω := by
  constructor
  · intro h
    exact ⟨(twoInfiniteClusters_permConfig_iff φ ω).1 h.1,
      fun hthree => h.2 ((threeInfiniteClusters_permConfig_iff φ ω).2 hthree)⟩
  · intro h
    exact ⟨(twoInfiniteClusters_permConfig_iff φ ω).2 h.1,
      fun hthree => h.2 ((threeInfiniteClusters_permConfig_iff φ ω).1 hthree)⟩

/-- **Ergodicity upgrades exactly-two exclusion to zero mass.**  This is an
explicit additional dynamical hypothesis, not a consequence of DLR equations
or mere measure preservation. -/
theorem measure_exactlyTwoInfiniteClusters_eq_zero_of_ergodic
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ]
    (hins : FinitePatternInsertionTolerance μ) (φ : G ≃g G)
    (herg : Ergodic (permConfig φ) μ) :
    μ {ω | ExactlyTwoInfiniteClusters G ω} = 0 := by
  have hmeas : MeasurableSet {ω | ExactlyTwoInfiniteClusters G ω} :=
    measurableSet_exactlyTwoInfiniteClusters
  have hpre : permConfig φ ⁻¹' {ω | ExactlyTwoInfiniteClusters G ω} =
      {ω | ExactlyTwoInfiniteClusters G ω} := by
    ext ω
    exact exactlyTwoInfiniteClusters_permConfig_iff φ ω
  have hpre_ae : permConfig φ ⁻¹' {ω | ExactlyTwoInfiniteClusters G ω} =ᵐ[μ]
      {ω | ExactlyTwoInfiniteClusters G ω} := by
    rw [hpre]
  rcases herg.toPreErgodic.prob_eq_zero_or_one hmeas.nullMeasurableSet hpre_ae with hzero | hone
  · exact hzero
  · have hp : Measurable (fun ω => ExactlyTwoInfiniteClusters G ω) :=
      measurableSet_setOfPred.mp hmeas
    have hae : ∀ᵐ ω ∂μ, ExactlyTwoInfiniteClusters G ω :=
      (ae_iff_prob_eq_one hp).2 hone
    exact (not_ae_exactlyTwoInfiniteClusters_of_insertionTolerant hG μ hins hae).elim

/-- Interior-rate `q = 1` source-law exactly-two exclusion under one ergodic
automorphism. -/
theorem measure_exactlyTwoInfiniteClusters_eq_zero_of_ergodic_q_one
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (X : VertexExhaustion V) {p : NNReal} (hp : p ≤ 1)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ SourceFKMeasures (G := G) zero_lt_one hp)
    (φ : G ≃g G) (herg : Ergodic (permConfig φ) (μ : Measure _)) :
    (μ : Measure (Configuration G.edgeSet)) {ω | ExactlyTwoInfiniteClusters G ω} = 0 := by
  have heq := eq_bernoulliConst_of_mem_sourceFKMeasures_q_one X hp hμ
  have hins : FinitePatternInsertionTolerance (μ : Measure (Configuration G.edgeSet)) := by
    rw [heq]
    exact finitePatternInsertionTolerance_bernoulliProduct
      (FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp)
      (by simpa [FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN] using hp0)
      (by simpa [FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN] using hp1)
  exact measure_exactlyTwoInfiniteClusters_eq_zero_of_ergodic hG (μ : Measure _) hins φ herg

/-- Interior-rate `q = 1` source laws cannot be in an almost-sure exactly-two
phase, even without an ergodicity or shift-invariance hypothesis. -/
theorem not_ae_exactlyTwoInfiniteClusters_q_one
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (X : VertexExhaustion V) {p : NNReal} (hp : p ≤ 1)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ SourceFKMeasures (G := G) zero_lt_one hp) :
    ¬ (∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ExactlyTwoInfiniteClusters G ω) := by
  have heq := eq_bernoulliConst_of_mem_sourceFKMeasures_q_one X hp hμ
  have hins : FinitePatternInsertionTolerance (μ : Measure (Configuration G.edgeSet)) := by
    rw [heq]
    exact finitePatternInsertionTolerance_bernoulliProduct
      (FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp)
      (by simpa [FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN] using hp0)
      (by simpa [FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN] using hp1)
  exact not_ae_exactlyTwoInfiniteClusters_of_insertionTolerant hG (μ : Measure _) hins

end FK.BurtonKeane.Automorphism


#print axioms FK.BurtonKeane.Automorphism.not_ae_exactlyTwoInfiniteClusters_q_one
#print axioms FK.BurtonKeane.Automorphism.measurePreserving_piCongrLeft_percolation
#print axioms FK.BurtonKeane.Automorphism.eq_bernoulliConst_of_mem_sourceFKMeasures_q_one
#print axioms FK.BurtonKeane.Automorphism.measurePreserving_permConfig_of_mem_sourceFKMeasures_q_one
#print axioms FK.BurtonKeane.Automorphism.dist_iso
#print axioms FK.BurtonKeane.Automorphism.threeWayArms_permConfig_iff
#print axioms FK.BurtonKeane.Automorphism.openInternal_image_permConfig
#print axioms FK.BurtonKeane.Automorphism.measurableSet_patchedEncounterAt
#print axioms FK.BurtonKeane.Automorphism.homogeneousPatchedEncounterEvents
#print axioms FK.BurtonKeane.Automorphism.measure_threeInfiniteClusters_eq_zero_of_folner
#print axioms FK.BurtonKeane.Automorphism.measure_threeInfiniteClusters_eq_zero_of_folner_q_one
#print axioms FK.BurtonKeane.Automorphism.exists_openInternal_globalAtMostOne_of_exactlyTwo
#print axioms FK.BurtonKeane.Automorphism.not_ae_exactlyTwoInfiniteClusters_of_insertionTolerant
#print axioms FK.BurtonKeane.Automorphism.measurableSet_exactlyTwoInfiniteClusters
#print axioms FK.BurtonKeane.Automorphism.measure_exactlyTwoInfiniteClusters_eq_zero_of_ergodic
#print axioms FK.BurtonKeane.Automorphism.measure_exactlyTwoInfiniteClusters_eq_zero_of_ergodic_q_one
