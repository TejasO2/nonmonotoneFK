import FK.NonlocalGeometry

/-!
# Explicit finite determination of exterior boundary conventions

Section 5.2 of Beffara--Faipeur--Oke uses the following fact when applying
finite planar duality to an infinite-graph exterior configuration.  At a
configuration with at most one infinite open component touching a finite
boundary, the whole boundary partition is determined by finitely many edges.
Connected pairs contribute a finite open path.  For a disconnected pair, at
least one side has finite component, and that component has finite incident
edge support by local finiteness.

The public `NonlocalGeometry` development proves the topological
local-constancy consequence.  This file gives the explicit finite edge support
and proves stability under every perturbation away from that support.  The
final theorem applies to every convention satisfying the paper's two exterior
component requirements, not merely to the free component partition.
-/

open Filter Set Topology
open scoped Classical

namespace FK.InfiniteVolume.FiniteExteriorDetermination

open CurvatureVariance.Infra.Percolation
open ConventionGeometry
open ConventionTransport
open NonlocalInterior

noncomputable section

variable {V W : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The incident-edge support of the component of `x`, when that component is
finite.  It is empty otherwise. -/
def rootSupport (ω : G.edgeSet → Bool) (x : V) : Set G.edgeSet :=
  if h : {y | OpenConnected G ω Set.univ x y}.Finite then
    clusterSupport {y | OpenConnected G ω Set.univ x y}
  else ∅

/-- A chosen open path between `x` and `y`, when they are connected. -/
def pairSupport (ω : G.edgeSet → Bool) (x y : V) : Set G.edgeSet :=
  if h : OpenConnected G ω Set.univ x y then walkSupport h.choose else ∅

/-- One finite edge support determining all open-component relations on the
finite boundary `b`. -/
def determiningSupport (b : W → V) (ω : G.edgeSet → Bool) : Set G.edgeSet :=
  (⋃ x, rootSupport ω (b x)) ∪ (⋃ x, ⋃ y, pairSupport ω (b x) (b y))

lemma finite_rootSupport (ω : G.edgeSet → Bool) (x : V) :
    (rootSupport ω x).Finite := by
  unfold rootSupport
  split_ifs with h
  · exact finite_clusterSupport h
  · exact Set.finite_empty

lemma finite_pairSupport (ω : G.edgeSet → Bool) (x y : V) :
    (pairSupport ω x y).Finite := by
  unfold pairSupport
  split_ifs with h
  · exact finite_walkSupport h.choose
  · exact Set.finite_empty

lemma finite_determiningSupport [Finite W] (b : W → V) (ω : G.edgeSet → Bool) :
    (determiningSupport b ω).Finite := by
  apply Set.Finite.union
  · exact Set.finite_iUnion fun x => finite_rootSupport ω (b x)
  · exact Set.finite_iUnion fun x =>
      Set.finite_iUnion fun y => finite_pairSupport ω (b x) (b y)

lemma rootSupport_subset_determiningSupport (b : W → V) (ω : G.edgeSet → Bool)
    (x : W) : rootSupport ω (b x) ⊆ determiningSupport b ω := by
  intro e he
  exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨x, he⟩)

lemma pairSupport_subset_determiningSupport (b : W → V) (ω : G.edgeSet → Bool)
    (x y : W) : pairSupport ω (b x) (b y) ⊆ determiningSupport b ω := by
  intro e he
  exact Set.mem_union_right _ (Set.mem_iUnion.mpr
    ⟨x, Set.mem_iUnion.mpr ⟨y, he⟩⟩)

/-- A connection present in `ω` survives every change off the determining
support, using the selected witness path. -/
lemma openConnected_of_agree_determiningSupport
    (b : W → V) {ω ζ : G.edgeSet → Bool}
    (hagree : ∀ e ∈ determiningSupport b ω, ω e = ζ e) {x y : W}
    (hxy : OpenConnected G ω Set.univ (b x) (b y)) :
    OpenConnected G ζ Set.univ (b x) (b y) := by
  apply openConnected_of_agree_walkSupport hxy.choose hxy.choose_spec
  intro e he
  apply hagree e
  apply pairSupport_subset_determiningSupport b ω x y
  unfold pairSupport
  rw [dif_pos hxy]
  exact he

/-- At a finite component, the determining support contains the component's
whole incident-edge boundary, so the component is unchanged by every
perturbation off that support. -/
lemma openConnected_iff_of_agree_determiningSupport_of_finite
    (b : W → V) {ω ζ : G.edgeSet → Bool}
    (hagree : ∀ e ∈ determiningSupport b ω, ω e = ζ e) {x : W}
    (hfin : {z | OpenConnected G ω Set.univ (b x) z}.Finite) (z : V) :
    OpenConnected G ω Set.univ (b x) z ↔ OpenConnected G ζ Set.univ (b x) z := by
  apply openConnected_iff_of_agree_clusterSupport
  intro e he
  apply hagree e
  apply rootSupport_subset_determiningSupport b ω x
  unfold rootSupport
  rw [dif_pos hfin]
  exact he

/-- Exact stability of every boundary connection relation.  For the reverse
implication, if both original components were infinite then at-most-one would
force a connection.  Otherwise a finite component supplies the obstruction. -/
lemma openConnected_iff_of_agree_determiningSupport
    (b : W → V) {ω ζ : G.edgeSet → Bool}
    (hagree : ∀ e ∈ determiningSupport b ω, ω e = ζ e)
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G ω Set.univ b)
      (fun x => ExteriorInfiniteCluster G ω Set.univ (b x))) (x y : W) :
    OpenConnected G ω Set.univ (b x) (b y) ↔
      OpenConnected G ζ Set.univ (b x) (b y) := by
  constructor
  · exact openConnected_of_agree_determiningSupport b hagree
  · intro hζ
    by_contra hω
    by_cases hx : ExteriorInfiniteCluster G ω Set.univ (b x)
    · have hy : ¬ ExteriorInfiniteCluster G ω Set.univ (b y) :=
        fun hy => hω (hunique x y hx hy)
      have hyfin : {z | OpenConnected G ω Set.univ (b y) z}.Finite :=
        Set.not_infinite.mp hy
      have hyx : OpenConnected G ω Set.univ (b y) (b x) :=
        (openConnected_iff_of_agree_determiningSupport_of_finite b hagree hyfin
          (b x)).mpr (openConnected_symm hζ)
      exact hω (openConnected_symm hyx)
    · have hxfin : {z | OpenConnected G ω Set.univ (b x) z}.Finite :=
        Set.not_infinite.mp hx
      exact hω ((openConnected_iff_of_agree_determiningSupport_of_finite b hagree
        hxfin (b y)).mpr hζ)

/-- The free exterior-open-component setoid is determined on the explicit
finite support. -/
theorem openPathSetoid_eq_of_agree_determiningSupport
    (b : W → V) {ω ζ : G.edgeSet → Bool}
    (hagree : ∀ e ∈ determiningSupport b ω, ω e = ζ e)
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G ω Set.univ b)
      (fun x => ExteriorInfiniteCluster G ω Set.univ (b x))) :
    openPathSetoid G ω Set.univ b = openPathSetoid G ζ Set.univ b := by
  apply Setoid.ext
  exact openConnected_iff_of_agree_determiningSupport b hagree hunique

/-- **Finite determination of every source-geometric convention.**  At an
at-most-one-cluster configuration, all its boundary relations are unchanged by
arbitrary edits off `determiningSupport`. -/
theorem setoid_eq_of_geometric_of_agree_determiningSupport
    (b : W → V) (α : (G.edgeSet → Bool) → Setoid W) {ω ζ : G.edgeSet → Bool}
    (hgeom : ∀ ξ, MergesOpenComponents (openPathSetoid G ξ Set.univ b) (α ξ) ∧
      SeparatesFiniteComponents (openPathSetoid G ξ Set.univ b) (α ξ)
        (fun x => ExteriorInfiniteCluster G ξ Set.univ (b x)))
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G ω Set.univ b)
      (fun x => ExteriorInfiniteCluster G ω Set.univ (b x)))
    (hagree : ∀ e ∈ determiningSupport b ω, ω e = ζ e) : α ζ = α ω := by
  apply Setoid.ext
  intro x y
  have hconn : OpenConnected G ω Set.univ (b x) (b y) ↔
      OpenConnected G ζ Set.univ (b x) (b y) :=
    openConnected_iff_of_agree_determiningSupport b hagree hunique x y
  by_cases hxy : OpenConnected G ω Set.univ (b x) (b y)
  · have hζ : OpenConnected G ζ Set.univ (b x) (b y) := hconn.mp hxy
    exact ⟨fun _ => (hgeom ω).1 hxy, fun _ => (hgeom ζ).1 hζ⟩
  · have hζ : ¬ OpenConnected G ζ Set.univ (b x) (b y) := fun h => hxy (hconn.mpr h)
    by_cases hx : ExteriorInfiniteCluster G ω Set.univ (b x)
    · have hy : ¬ ExteriorInfiniteCluster G ω Set.univ (b y) :=
        fun hy => hxy (hunique x y hx hy)
      have hyfin : {z | OpenConnected G ω Set.univ (b y) z}.Finite :=
        Set.not_infinite.mp hy
      have hset : {z | OpenConnected G ω Set.univ (b y) z} =
          {z | OpenConnected G ζ Set.univ (b y) z} := by
        ext z
        exact openConnected_iff_of_agree_determiningSupport_of_finite b hagree hyfin z
      have hyζ : ¬ ExteriorInfiniteCluster G ζ Set.univ (b y) := by
        unfold ExteriorInfiniteCluster
        rw [← hset]
        exact hy
      exact ⟨fun h => ((hgeom ζ).2 hζ (Or.inr hyζ) h).elim,
        fun h => ((hgeom ω).2 hxy (Or.inr hy) h).elim⟩
    · have hxfin : {z | OpenConnected G ω Set.univ (b x) z}.Finite :=
        Set.not_infinite.mp hx
      have hset : {z | OpenConnected G ω Set.univ (b x) z} =
          {z | OpenConnected G ζ Set.univ (b x) z} := by
        ext z
        exact openConnected_iff_of_agree_determiningSupport_of_finite b hagree hxfin z
      have hxζ : ¬ ExteriorInfiniteCluster G ζ Set.univ (b x) := by
        unfold ExteriorInfiniteCluster
        rw [← hset]
        exact hx
      exact ⟨fun h => ((hgeom ζ).2 hζ (Or.inl hxζ) h).elim,
        fun h => ((hgeom ω).2 hxy (Or.inl hx) h).elim⟩

/-- Every genuine edge exhaustion contains a finite window determining the
whole convention at the given at-most-one-cluster configuration.  Agreement on
that one window is enough; later boxes need not be searched separately. -/
theorem exists_exhaustion_box_determining_convention [Finite W]
    (exh : BoxExhaustion G.edgeSet)
    (b : W → V) (α : (G.edgeSet → Bool) → Setoid W) (ω : G.edgeSet → Bool)
    (hgeom : ∀ ξ, MergesOpenComponents (openPathSetoid G ξ Set.univ b) (α ξ) ∧
      SeparatesFiniteComponents (openPathSetoid G ξ Set.univ b) (α ξ)
        (fun x => ExteriorInfiniteCluster G ξ Set.univ (b x)))
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G ω Set.univ b)
      (fun x => ExteriorInfiniteCluster G ω Set.univ (b x))) :
    ∃ n : ℕ, ∀ ζ : G.edgeSet → Bool,
      (∀ e ∈ (exh.box n).edges, ω e = ζ e) →
        openPathSetoid G ω Set.univ b = openPathSetoid G ζ Set.univ b ∧ α ζ = α ω := by
  obtain ⟨n, hn⟩ := (exh.eventually_subset
    (finite_determiningSupport b ω).toFinset).exists
  refine ⟨n, fun ζ hagree => ?_⟩
  have hagree' : ∀ e ∈ determiningSupport b ω, ω e = ζ e := by
    intro e he
    apply hagree e
    exact hn ((finite_determiningSupport b ω).mem_toFinset.mpr he)
  exact ⟨openPathSetoid_eq_of_agree_determiningSupport b hagree' hunique,
    setoid_eq_of_geometric_of_agree_determiningSupport b α hgeom hunique hagree'⟩

/-- Package the finite witness, the free component identity, and the identity
for every geometric convention. -/
theorem exists_finite_support_determining_convention [Finite W]
    (b : W → V) (α : (G.edgeSet → Bool) → Setoid W) (ω : G.edgeSet → Bool)
    (hgeom : ∀ ξ, MergesOpenComponents (openPathSetoid G ξ Set.univ b) (α ξ) ∧
      SeparatesFiniteComponents (openPathSetoid G ξ Set.univ b) (α ξ)
        (fun x => ExteriorInfiniteCluster G ξ Set.univ (b x)))
    (hunique : AtMostOneInfiniteCluster (openPathSetoid G ω Set.univ b)
      (fun x => ExteriorInfiniteCluster G ω Set.univ (b x))) :
    ∃ D : Set G.edgeSet, D.Finite ∧ ∀ ζ : G.edgeSet → Bool,
      (∀ e ∈ D, ω e = ζ e) →
        openPathSetoid G ω Set.univ b = openPathSetoid G ζ Set.univ b ∧ α ζ = α ω := by
  refine ⟨determiningSupport b ω, finite_determiningSupport b ω, ?_⟩
  intro ζ hagree
  exact ⟨openPathSetoid_eq_of_agree_determiningSupport b hagree hunique,
    setoid_eq_of_geometric_of_agree_determiningSupport b α hgeom hunique hagree⟩

end

end FK.InfiniteVolume.FiniteExteriorDetermination
