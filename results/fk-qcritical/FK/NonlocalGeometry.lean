import FK.InteriorWeakLimit
import CurvatureVariance.Infra.Percolation.Balls

/-!
# Nonlocal exterior geometry at at-most-one-cluster configurations

At a configuration with at most one infinite exterior cluster, every
geometrically valid boundary assignment is locally constant.  The proof uses
finite open paths for connected pairs and the finite incident-edge boundary of
a finite component for disconnected pairs.  No uniqueness hypothesis is
needed at the nearby configurations.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.NonlocalInterior

open CurvatureVariance.Infra.Percolation
open ConventionGeometry
open ConventionTransport

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-- The finitely many graph edges traversed by a walk. -/
def walkSupport {x y : V} (p : G.Walk x y) : Set G.edgeSet :=
  Subtype.val ⁻¹' ↑(p.darts.toFinset.image fun d => d.edge)

lemma finite_walkSupport {x y : V} (p : G.Walk x y) :
    (walkSupport p).Finite := by
  exact (p.darts.toFinset.image fun d => d.edge).finite_toSet.preimage
    Subtype.val_injective.injOn

lemma mem_walkSupport {x y : V} (p : G.Walk x y) (d : G.Dart)
    (hd : d ∈ p.darts) : (⟨d.edge, d.edge_mem⟩ : G.edgeSet) ∈ walkSupport p := by
  change d.edge ∈ p.darts.toFinset.image (fun d => d.edge)
  exact Finset.mem_image.mpr ⟨d, List.mem_toFinset.mpr hd, rfl⟩

/-- The graph edges incident to a prescribed set of vertices. -/
def clusterSupport (C : Set V) : Set G.edgeSet :=
  {e | ∃ x ∈ C, x ∈ e.1}

lemma finite_clusterSupport [G.LocallyFinite] {C : Set V} (hC : C.Finite) :
    (clusterSupport (G := G) C).Finite := by
  classical
  have hS : (⋃ x ∈ C, G.incidenceSet x).Finite :=
    hC.biUnion fun x _ => (G.incidenceSet x).toFinite
  refine (hS.preimage Subtype.val_injective.injOn).subset ?_
  rintro e ⟨x, hx, hxe⟩
  exact Set.mem_biUnion hx ⟨e.2, hxe⟩

/-- A path remains open after a perturbation fixing its finite support. -/
lemma openConnected_of_agree_walkSupport {ω ζ : G.edgeSet → Bool} {x y : V}
    (p : G.Walk x y) (hp : IsOpenIn ω Set.univ p)
    (h : ∀ e ∈ walkSupport p, ω e = ζ e) :
    OpenConnected G ζ Set.univ x y := by
  refine ⟨p, fun d hd => ⟨Set.mem_univ _, ?_⟩⟩
  rw [← h _ (mem_walkSupport p d hd)]
  exact (hp d hd).2

/-- If `C` is the open component of `x` in `ω`, connections from a vertex of
`C` along a `ζ`-open path remain in `C` whenever the two configurations agree
on the incident-edge support of `C`. -/
lemma openConnected_of_agree_clusterSupport {ω ζ : G.edgeSet → Bool} {x a z : V}
    (ha : OpenConnected G ω Set.univ x a)
    (p : G.Walk a z) (hp : IsOpenIn ζ Set.univ p)
    (h : ∀ e ∈ clusterSupport {y | OpenConnected G ω Set.univ x y}, ω e = ζ e) :
    OpenConnected G ω Set.univ x z := by
  revert ha
  induction p with
  | nil => exact id
  | @cons a b c hab p ih =>
      intro ha
      rw [isOpenIn_cons] at hp
      have he : (⟨s(a, b), hab⟩ : G.edgeSet) ∈
          clusterSupport {y | OpenConnected G ω Set.univ x y} :=
        ⟨a, ha, by simp⟩
      have hopen : ω ⟨s(a, b), hab⟩ = true := by
        rw [h _ he]
        exact hp.1.2
      exact ih hp.2 (ha.trans (OpenConnected.of_adj hab (Set.mem_univ _) hopen))

/-- A finite component, and hence finiteness of that component, is stable
under perturbations fixing its incident-edge support. -/
lemma openConnected_iff_of_agree_clusterSupport {ω ζ : G.edgeSet → Bool} {x z : V}
    (h : ∀ e ∈ clusterSupport {y | OpenConnected G ω Set.univ x y}, ω e = ζ e) :
    OpenConnected G ω Set.univ x z ↔ OpenConnected G ζ Set.univ x z := by
  have hsub : {y | OpenConnected G ζ Set.univ x y} ⊆
      {y | OpenConnected G ω Set.univ x y} := by
    rintro y ⟨p, hp⟩
    exact openConnected_of_agree_clusterSupport (OpenConnected.refl ω Set.univ x)
      p hp h
  constructor
  · rintro ⟨p, hp⟩
    apply openConnected_of_agree_clusterSupport (ω := ζ) (ζ := ω)
      (OpenConnected.refl ζ Set.univ x) p hp
    intro e he
    apply (h e ?_).symm
    obtain ⟨a, ha, hae⟩ := he
    exact ⟨a, hsub ha, hae⟩
  · exact fun hz => hsub hz

lemma eventually_not_openConnected_of_finite [G.LocallyFinite]
    (ω : G.edgeSet → Bool) (x y : V)
    (hfin : {z | OpenConnected G ω Set.univ x z}.Finite)
    (hxy : ¬ OpenConnected G ω Set.univ x y) :
    ∀ᶠ ζ in 𝓝 ω, ¬ OpenConnected G ζ Set.univ x y := by
  have hU : (clusterSupport {z | OpenConnected G ω Set.univ x z}).pi
      (fun e => {ω e}) ∈ 𝓝 ω :=
    set_pi_mem_nhds (finite_clusterSupport hfin) fun _ _ => by simp
  filter_upwards [hU] with ζ hζ hconn
  exact hxy ((openConnected_iff_of_agree_clusterSupport
    (fun e he => (hζ e he).symm)).mpr hconn)

/-- Both connection and finiteness of a finite component hold on a fixed
finite-coordinate neighbourhood. -/
lemma eventually_finite_component_eq [G.LocallyFinite]
    (ω : G.edgeSet → Bool) (x : V)
    (hfin : {z | OpenConnected G ω Set.univ x z}.Finite) :
    ∀ᶠ ζ in 𝓝 ω, {z | OpenConnected G ζ Set.univ x z} =
      {z | OpenConnected G ω Set.univ x z} := by
  have hU : (clusterSupport {z | OpenConnected G ω Set.univ x z}).pi
      (fun e => {ω e}) ∈ 𝓝 ω :=
    set_pi_mem_nhds (finite_clusterSupport hfin) fun _ _ => by simp
  filter_upwards [hU] with ζ hζ
  ext z
  exact (openConnected_iff_of_agree_clusterSupport (ω := ω) (ζ := ζ) (x := x) (z := z)
    (fun e he => (hζ e he).symm)).symm

/-- Geometric partitions are locally constant along any continuous map into
configuration space at an at-most-one-cluster image. -/
lemma eventually_rel_of_geometric_comap {X W : Type*} [TopologicalSpace X]
    [G.LocallyFinite] (config : X → G.edgeSet → Bool) (hconfig : Continuous config)
    (b : W → V) (α : X → Setoid W) (x₀ : X)
    (hgeom : ∀ z, MergesOpenComponents (openPathSetoid G (config z) Set.univ b) (α z) ∧
      SeparatesFiniteComponents (openPathSetoid G (config z) Set.univ b) (α z)
        (fun x => ExteriorInfiniteCluster G (config z) Set.univ (b x)))
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G (config x₀) Set.univ b)
      (fun x => ExteriorInfiniteCluster G (config x₀) Set.univ (b x)))
    (x y : W) :
    ∀ᶠ z in 𝓝 x₀, (α z).r x y ↔ (α x₀).r x y := by
  by_cases hxy : OpenConnected G (config x₀) Set.univ (b x) (b y)
  · have hxyω := hxy
    obtain ⟨p, hp⟩ := hxy
    have hU : (walkSupport p).pi (fun e => {config x₀ e}) ∈ 𝓝 (config x₀) :=
      set_pi_mem_nhds (finite_walkSupport p) fun _ _ => by simp
    filter_upwards [hconfig.continuousAt hU] with z hz
    have hconn : OpenConnected G (config z) Set.univ (b x) (b y) :=
      openConnected_of_agree_walkSupport p hp fun e he => (hz e he).symm
    exact ⟨fun _ => (hgeom x₀).1 hxyω, fun _ => (hgeom z).1 hconn⟩
  · by_cases hx : ExteriorInfiniteCluster G (config x₀) Set.univ (b x)
    · have hy : ¬ ExteriorInfiniteCluster G (config x₀) Set.univ (b y) :=
        fun hy => hxy (hunique x y hx hy)
      have hyfin : {w | OpenConnected G (config x₀) Set.univ (b y) w}.Finite :=
        Set.not_infinite.mp hy
      filter_upwards [hconfig.continuousAt
        (eventually_finite_component_eq (config x₀) (b y) hyfin)] with z hz
      have hconn : ¬ OpenConnected G (config z) Set.univ (b x) (b y) := by
        intro hc
        have hc' : OpenConnected G (config z) Set.univ (b y) (b x) :=
          openConnected_symm hc
        have hc'' : OpenConnected G (config x₀) Set.univ (b y) (b x) :=
          (Set.ext_iff.mp hz (b x)).mp hc'
        exact hxy (openConnected_symm hc'')
      have hy' : ¬ ExteriorInfiniteCluster G (config z) Set.univ (b y) := by
        unfold ExteriorInfiniteCluster
        rw [hz]
        exact hy
      exact ⟨fun hα => ((hgeom z).2 hconn (Or.inr hy') hα).elim,
        fun hα => ((hgeom x₀).2 hxy (Or.inr hy) hα).elim⟩
    · have hxfin : {w | OpenConnected G (config x₀) Set.univ (b x) w}.Finite :=
        Set.not_infinite.mp hx
      filter_upwards [hconfig.continuousAt
        (eventually_finite_component_eq (config x₀) (b x) hxfin)] with z hz
      have hconn : ¬ OpenConnected G (config z) Set.univ (b x) (b y) := by
        intro hc
        exact hxy ((Set.ext_iff.mp hz (b y)).mp hc)
      have hx' : ¬ ExteriorInfiniteCluster G (config z) Set.univ (b x) := by
        unfold ExteriorInfiniteCluster
        rw [hz]
        exact hx
      exact ⟨fun hα => ((hgeom z).2 hconn (Or.inl hx') hα).elim,
        fun hα => ((hgeom x₀).2 hxy (Or.inl hx) hα).elim⟩

/-- Nonlocal geometric partitions are locally constant along a continuous map
at each at-most-one-infinite-cluster image. -/
theorem eventually_setoid_eq_of_geometric_comap {X W : Type*} [TopologicalSpace X]
    [Finite W] [G.LocallyFinite] (config : X → G.edgeSet → Bool)
    (hconfig : Continuous config) (b : W → V) (α : X → Setoid W) (x₀ : X)
    (hgeom : ∀ z, MergesOpenComponents (openPathSetoid G (config z) Set.univ b) (α z) ∧
      SeparatesFiniteComponents (openPathSetoid G (config z) Set.univ b) (α z)
        (fun x => ExteriorInfiniteCluster G (config z) Set.univ (b x)))
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G (config x₀) Set.univ b)
      (fun x => ExteriorInfiniteCluster G (config x₀) Set.univ (b x))) :
    ∀ᶠ z in 𝓝 x₀, α z = α x₀ := by
  filter_upwards [(Filter.eventually_all).2 fun x => (Filter.eventually_all).2
    (eventually_rel_of_geometric_comap config hconfig b α x₀ hgeom hunique x)] with z hz
  exact Setoid.ext (fun x y => hz x y)

/-- Nonlocal geometric partitions are locally constant at each
at-most-one-infinite-cluster point of the configuration space. -/
theorem eventually_setoid_eq_of_geometric {W : Type*} [Finite W] [G.LocallyFinite]
    (b : W → V) (α : (G.edgeSet → Bool) → Setoid W) (ω : G.edgeSet → Bool)
    (hgeom : ∀ ξ, MergesOpenComponents (openPathSetoid G ξ Set.univ b) (α ξ) ∧
      SeparatesFiniteComponents (openPathSetoid G ξ Set.univ b) (α ξ)
        (fun x => ExteriorInfiniteCluster G ξ Set.univ (b x)))
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G ω Set.univ b)
      (fun x => ExteriorInfiniteCluster G ω Set.univ (b x))) :
    ∀ᶠ ζ in 𝓝 ω, α ζ = α ω := by
  exact eventually_setoid_eq_of_geometric_comap id continuous_id b α ω hgeom hunique

/-- Pulling the preceding result back through closing a box's interior shows
that every geometrically valid box assignment is locally constant at each
exterior configuration with at most one infinite exterior component. -/
theorem eventually_partition_eq_of_atMostOne {box : ℕ → FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G box) [Countable V] [G.LocallyFinite]
    (Φ : BoundaryAssignment box) (hΦ : IsGeometric data.geometry Φ)
    (n : ℕ) (η : (box n).Exterior)
    (hunique : AtMostOneInfiniteCluster (data.geometry.components n η)
      (data.geometry.infinite n η)) :
    ∀ᶠ ζ in 𝓝 η, Φ.partition n ζ = Φ.partition n η := by
  have hclose : Continuous (closeInside (box n)) :=
    (InteriorWeakLimit.FiniteBox.continuous_glue (box n)).comp
      (continuous_id.prodMk continuous_const)
  apply eventually_setoid_eq_of_geometric_comap (closeInside (box n)) hclose
    (data.vertex n) (Φ.partition n) η
  · intro ζ
    refine ⟨hΦ.1 n ζ, ?_⟩
    intro x y hxy hfin
    exact hΦ.2 n ζ hxy hfin
  · exact hunique

end

end FK.InfiniteVolume.NonlocalInterior
