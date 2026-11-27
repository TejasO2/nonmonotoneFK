import FK.AGSourceHypotheses

/-!
# Transport of enhancement density to a plane dual

The proof of Theorem 1.11 in Beffara--Faipeur--Oke reuses an enhanced edge
set on the planar dual.  This file proves the graph-theoretic density step
without assuming that the dual graph is quasi-transitive.

`UniformCornerBound` is the local statement supplied by a rotation system:
the two dual edges corresponding to primal edges at a common vertex can be
joined in the dual line graph, with a uniform bound on the distance.  It is
strictly weaker than asserting the desired global comparison.  We telescope
these local bounds along a primal line-graph walk and transport
`FK.Theorem14.BoundedDistance` to the same edge labels in the dual.

No double-ray/essentialness conclusion, finite-volume duality, AG strict
shift, or strong-uniqueness conclusion is asserted here.
-/

namespace FK.Planar.DualEnhancement

open Set
open scoped SimpleGraph Sym2

universe u v

variable {V : Type u} {F : Type v} {G : SimpleGraph V} {GD : SimpleGraph F}

/-- A uniform local corner-link condition.  In a plane embedding this is the
finite rotation path around a common primal vertex.  Reachability is included
explicitly because natural-valued `SimpleGraph.dist` is zero between distinct
vertices in different components. -/
def UniformCornerBound (edge : G.edgeSet ≃ GD.edgeSet) (K : ℕ) : Prop :=
  ∀ e f : G.edgeSet, (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) →
    GD.lineGraph.Reachable (edge e) (edge f) ∧
      GD.lineGraph.dist (edge e) (edge f) ≤ K

/-- Vertex-indexed corner links.  A finite rotation cycle around `v` supplies
this with `K v` at most the number of incident edges, so no global bound on
face degrees or any dual automorphism action is needed. -/
def VertexCornerBound (edge : G.edgeSet ≃ GD.edgeSet) (K : V → ℕ) : Prop :=
  ∀ (e f : G.edgeSet) (v : V), v ∈ (e : Sym2 V) → v ∈ (f : Sym2 V) →
    GD.lineGraph.Reachable (edge e) (edge f) ∧
      GD.lineGraph.dist (edge e) (edge f) ≤ K v

/-- A uniform degree/diameter bound upgrades local rotation cycles to a
uniform corner bound. -/
lemma VertexCornerBound.uniform {edge : G.edgeSet ≃ GD.edgeSet}
    {K : V → ℕ} (h : VertexCornerBound edge K) {Δ : ℕ}
    (hΔ : ∀ v, K v ≤ Δ) : UniformCornerBound edge Δ := by
  rintro e f ⟨v, he, hf⟩
  obtain ⟨hreach, hdist⟩ := h e f v he hf
  exact ⟨hreach, hdist.trans (hΔ v)⟩

namespace UniformCornerBound

variable {edge : G.edgeSet ≃ GD.edgeSet} {K : ℕ}

/-- The condition applies in particular to one step of the primal line graph. -/
lemma of_adj (h : UniformCornerBound edge K) {e f : G.edgeSet}
    (hef : G.lineGraph.Adj e f) :
    GD.lineGraph.Reachable (edge e) (edge f) ∧
      GD.lineGraph.dist (edge e) (edge f) ≤ K :=
  h e f (SimpleGraph.lineGraph_adj_iff_exists.mp hef).2

/-- The images of a primal line-graph walk are reachable in the dual line graph. -/
lemma reachable_map_of_walk (h : UniformCornerBound edge K)
    {e f : G.edgeSet} (w : G.lineGraph.Walk e f) :
    GD.lineGraph.Reachable (edge e) (edge f) := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons e a f hea w ih => exact (h.of_adj hea).1.trans ih

/-- Telescoping local rotation bounds along a primal line-graph walk. -/
lemma dist_map_le_mul_length_of_walk (h : UniformCornerBound edge K)
    {e f : G.edgeSet} (w : G.lineGraph.Walk e f) :
    GD.lineGraph.dist (edge e) (edge f) ≤ K * w.length := by
  induction w with
  | nil => simp
  | @cons e a f hea w ih =>
      have hreach : GD.lineGraph.Reachable (edge e) (edge a) := (h.of_adj hea).1
      calc
        GD.lineGraph.dist (edge e) (edge f) ≤
            GD.lineGraph.dist (edge e) (edge a) +
              GD.lineGraph.dist (edge a) (edge f) :=
          hreach.dist_triangle_left _
        _ ≤ K + K * w.length := Nat.add_le_add (h.of_adj hea).2 ih
        _ = K * (w.length + 1) := by
          rw [Nat.mul_succ]
          exact Nat.add_comm K (K * w.length)

/-- The dual map of line-graph distances is Lipschitz whenever local corner
links have diameter at most `K`. -/
lemma dist_map_le_mul (h : UniformCornerBound edge K)
    {e f : G.edgeSet} (hre : G.lineGraph.Reachable e f) :
    GD.lineGraph.dist (edge e) (edge f) ≤ K * G.lineGraph.dist e f := by
  obtain ⟨w, hw⟩ := hre.exists_walk_length_eq_dist
  rw [← hw]
  exact h.dist_map_le_mul_length_of_walk w

end UniformCornerBound

/-- The local corner condition is not arbitrary extra strength: it is exactly
equivalent to the global Lipschitz/reachability estimate for the induced map
of primal line-graph distances. -/
theorem lipschitz_iff_uniformCornerBound {edge : G.edgeSet ≃ GD.edgeSet} {K : ℕ} :
    (∀ e f : G.edgeSet, G.lineGraph.Reachable e f →
      GD.lineGraph.Reachable (edge e) (edge f) ∧
        GD.lineGraph.dist (edge e) (edge f) ≤ K * G.lineGraph.dist e f) ↔
      UniformCornerBound edge K := by
  constructor
  · intro h e f
    rintro ⟨v, he, hf⟩
    by_cases hef : e = f
    · subst f
      exact ⟨SimpleGraph.Reachable.refl _, by simp⟩
    have hadj : G.lineGraph.Adj e f :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hef, v, he, hf⟩
    obtain ⟨hreach, hdist⟩ := h e f hadj.reachable
    refine ⟨hreach, ?_⟩
    simpa [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] using hdist
  · intro h e f hre
    exact ⟨h.reachable_map_of_walk hre.some, h.dist_map_le_mul hre⟩

/-- Local corner links and a connected primal line graph make the whole dual
line graph connected.  This is a conclusion, not an extra dual connectedness
assumption in the density theorem. -/
lemma connected_of_uniformCornerBound
    {edge : G.edgeSet ≃ GD.edgeSet} {K : ℕ}
    (hcorner : UniformCornerBound edge K)
    (hconnected : G.lineGraph.Connected) : GD.lineGraph.Connected := by
  let _ : Nonempty GD.edgeSet := hconnected.nonempty.map edge
  refine ⟨fun ε η => ?_⟩
  have h := hcorner.reachable_map_of_walk
    ((hconnected (edge.symm ε) (edge.symm η)).some)
  simpa only [Equiv.apply_symm_apply] using h

/-- **Dual density without dual quasi-transitivity.**  Bounded-distance
enhancement density on the primal line graph transports to the image of the
same enhanced labels on the dual line graph. -/
theorem boundedDistance_image_of_uniformCornerBound
    {edge : G.edgeSet ≃ GD.edgeSet} {K : ℕ}
    (hcorner : UniformCornerBound edge K)
    (hconnected : G.lineGraph.Connected) (S : Set G.edgeSet)
    (hS : FK.Theorem14.BoundedDistance G.lineGraph.dist S) :
    FK.Theorem14.BoundedDistance GD.lineGraph.dist (edge '' S) := by
  obtain ⟨R, hR⟩ := hS
  refine ⟨K * R, fun ε => ?_⟩
  obtain ⟨e, heS, he⟩ := hR (edge.symm ε)
  refine ⟨edge e, ⟨e, heS, rfl⟩, ?_⟩
  have hdist := hcorner.dist_map_le_mul (hconnected (edge.symm ε) e)
  simpa only [Equiv.apply_symm_apply] using
    hdist.trans (Nat.mul_le_mul_left K he)

/-- Source-shaped form: only a uniform primal degree bound and the local
rotation/walk bound at each vertex are required. -/
theorem boundedDistance_image_of_vertexCornerBound
    {edge : G.edgeSet ≃ GD.edgeSet} {K : V → ℕ} {Δ : ℕ}
    (hcorner : VertexCornerBound edge K) (hΔ : ∀ v, K v ≤ Δ)
    (hconnected : G.lineGraph.Connected) (S : Set G.edgeSet)
    (hS : FK.Theorem14.BoundedDistance G.lineGraph.dist S) :
    FK.Theorem14.BoundedDistance GD.lineGraph.dist (edge '' S) :=
  boundedDistance_image_of_uniformCornerBound (hcorner.uniform hΔ) hconnected S hS

/-- Exact graph-hypothesis form for Theorem 1.10/1.11.  Primal
quasi-transitivity is used only to bound primal degrees.  The local rotation
bound is the sole geometric hypothesis; no quasi-transitivity, bounded-degree
or pivotal-edge hypothesis for `GD` is required for this density conclusion. -/
theorem boundedDistance_image_of_paperHypotheses
    [Countable V] [G.LocallyFinite] (o : V)
    (hG : FK.AGShift.PaperGraphHypotheses G o)
    {edge : G.edgeSet ≃ GD.edgeSet}
    (hcorner : VertexCornerBound edge (fun v => G.degree v)) (S : Set G.edgeSet)
    (hS : FK.Theorem14.BoundedDistance G.lineGraph.dist S) :
    FK.Theorem14.BoundedDistance GD.lineGraph.dist (edge '' S) := by
  let _ : Nonempty G.edgeSet := ⟨hG.pivotal.choose⟩
  have hLG : G.lineGraph.Connected :=
    FK.QuasiTransitive.lineGraph_connected G hG.connected
  obtain ⟨Δ, hΔ⟩ :=
    FK.QuasiTransitive.exists_degree_bound G hG.connected hG.quasiTransitive
  exact boundedDistance_image_of_vertexCornerBound hcorner hΔ hLG S hS

/-- The identity edge pairing is a simple non-vacuity check for the local
interface: incident edges are at distance at most one in the same line graph. -/
lemma uniformCornerBound_refl (G : SimpleGraph V) :
    UniformCornerBound (Equiv.refl G.edgeSet) 1 := by
  rintro e f ⟨v, he, hf⟩
  by_cases h : e = f
  · subst f
    exact ⟨SimpleGraph.Reachable.refl _, by simp⟩
  have hadj : G.lineGraph.Adj e f :=
    SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨h, v, he, hf⟩
  exact ⟨hadj.reachable, by
    simpa using (SimpleGraph.dist_eq_one_iff_adj.mpr hadj).le⟩

end FK.Planar.DualEnhancement
