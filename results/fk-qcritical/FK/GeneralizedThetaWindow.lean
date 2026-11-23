import FK.GeneralizedTheta
import FK.JordanUnicyclicEnclosure
import FK.FacialSubdivision

/-!
# Connected non-all-open spherical windows in generalized theta graphs

For two distinct branches `i,j` of a length-two generalized theta graph, the
union of those branches is an exact cycle-matroid circuit.  We realize that
circuit by four straight segments from two interior terminals to two exterior
internal vertices.  Every other branch is realized inside a strictly smaller
ball.  Thus the sphere of radius `3*a/4` is controlled precisely by the two
selected branches.  Opening exactly those branches produces a connected
spherical window, which is non-all-open whenever a third branch exists.

When the branch type is the edge type of a connected labelled cycle `G`, the
accepted bundled-cycle duality theorem supplies the exact plane-dual
certificate for the same theta graph.  The geometric construction is finite;
it does not claim a cofinal exhaustion of an infinite graph.
-/

namespace FK.PlaneTopology.GeneralizedThetaWindow

noncomputable section

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.GeneralizedTheta
open CurvatureVariance.Infra.Percolation
open FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

variable {ι : Type*} [Fintype ι]

/-- Terminals lie inside the sphere of radius `3*a/4`. -/
def terminal (a : ℝ) : Bool → ℝ × ℝ
  | false => (-a / 2, 0)
  | true => (a / 2, 0)

/-- The selected internal vertices lie outside the sphere; all others lie at
its centre. -/
def internal (i j : ι) (a : ℝ) (k : ι) : ℝ × ℝ :=
  if k = i then (0, a) else if k = j then (0, -a) else (0, 0)

/-- The embedding of the generalized theta vertices. -/
def vertex (i j : ι) (a : ℝ) : (lengthTwoTheta ι).Vertex → ℝ × ℝ
  | Sum.inl b => terminal a b
  | Sum.inr k => internal i j a k

/-- The two full branches selected for the outer circuit. -/
def selectedBranches (i j : ι) : Set (lengthTwoTheta ι).Edge :=
  branch i ∪ branch j

/-- Exactly the two selected branches are open. -/
def selectedConfig (i j : ι) : (lengthTwoTheta ι).Configuration :=
  (lengthTwoTheta ι).setConfig (selectedBranches i j)

lemma nonloop (e : (lengthTwoTheta ι).Edge) :
    (lengthTwoTheta ι).source e ≠ (lengthTwoTheta ι).target e := by
  simp [lengthTwoTheta]

lemma dist_terminal (a : ℝ) (ha : 0 ≤ a) (b : Bool) :
    dist (terminal a b) 0 = a / 2 := by
  have ha2 : 0 ≤ a / 2 := div_nonneg ha (by norm_num)
  cases b <;>
    simp [terminal, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg ha, abs_of_nonneg ha2, max_eq_left ha2]

lemma dist_internal_of_ne {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) (a : ℝ) :
    dist (internal i j a k) 0 = 0 := by
  simp [internal, hki, hkj]

lemma dist_internal_left (i j : ι) (a : ℝ) (ha : 0 ≤ a) :
    dist (internal i j a i) 0 = a := by
  simp [internal, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
    abs_of_nonneg ha, max_eq_right ha]

lemma dist_internal_right {i j : ι} (hij : i ≠ j) (a : ℝ) (ha : 0 ≤ a) :
    dist (internal i j a j) 0 = a := by
  simp [internal, hij.symm, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
    abs_of_nonneg ha, max_eq_right ha]

/-- No vertex lies on the separating sphere. -/
theorem vertex_off_sphere (i j : ι) (a : ℝ) (ha : 0 < a)
    (v : (lengthTwoTheta ι).Vertex) :
    vertex i j a v ∈ (sphere (0 : ℝ × ℝ) (3 * a / 4))ᶜ := by
  simp only [Set.mem_compl_iff, Metric.mem_sphere]
  cases v with
  | inl b =>
      rw [show vertex i j a (Sum.inl b) = terminal a b from rfl,
        dist_terminal a ha.le]
      linarith
  | inr k =>
      by_cases hki : k = i
      · subst k
        rw [show vertex i j a (Sum.inr i) = internal i j a i from rfl,
          dist_internal_left i j a ha.le]
        linarith
      · by_cases hkj : k = j
        · subst k
          have hij : i ≠ j := by
            intro h
            exact hki h.symm
          rw [show vertex i j a (Sum.inr j) = internal i j a j from rfl,
            dist_internal_right hij a ha.le]
          linarith
        · rw [show vertex i j a (Sum.inr k) = internal i j a k from rfl,
            dist_internal_of_ne hki hkj a]
          positivity

/-- Straight realization of a terminal-to-internal labelled segment. -/
noncomputable def branchArc (i j : ι) (a : ℝ) (k : ι) (b : Bool) :
    Path (terminal a b) (internal i j a k) :=
  straightPath _ _

/-- Path realization of the simple quotient.  Opposite adjacencies use the
reversed segment; impossible same-side adjacencies are eliminated using the
actual labelled endpoints. -/
noncomputable def realization (i j : ι) (a : ℝ) :
    OpenPathRealization (lengthTwoTheta ι).simpleGraph (vertex i j a) where
  arc := by
    intro u v huv
    cases u with
    | inl b =>
        cases v with
        | inl c =>
            exfalso
            obtain ⟨e, he⟩ := ((lengthTwoTheta ι).simpleGraph_adj_iff.mp huv).2
            rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> cases hs <;> cases ht
        | inr k => exact branchArc i j a k b
    | inr k =>
        cases v with
        | inl b => exact (branchArc i j a k b).symm
        | inr l =>
            exfalso
            obtain ⟨e, he⟩ := ((lengthTwoTheta ι).simpleGraph_adj_iff.mp huv).2
            rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> cases hs <;> cases ht

lemma realization_arc_inl_inr (i j : ι) (a : ℝ) (k : ι) (b : Bool)
    (h : (lengthTwoTheta ι).simpleGraph.Adj (Sum.inl b) (Sum.inr k)) (t : I) :
    (realization i j a).arc h t = branchArc i j a k b t := rfl

lemma realization_arc_inr_inl (i j : ι) (a : ℝ) (k : ι) (b : Bool)
    (h : (lengthTwoTheta ι).simpleGraph.Adj (Sum.inr k) (Sum.inl b)) (t : I) :
    (realization i j a).arc h t = branchArc i j a k b (unitInterval.symm t) := rfl

/-- Every unselected realized segment lies in the closed ball of radius
`a/2`, hence strictly inside the separating sphere. -/
theorem dist_arc_le_of_ne {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j)
    (a : ℝ) (ha : 0 ≤ a) (b : Bool) (t : I) :
    dist (branchArc i j a k b t) 0 ≤ a / 2 := by
  apply dist_straightPath_le
  · rw [dist_terminal a ha]
  · rw [dist_internal_of_ne hki hkj a]
    positivity

lemma simpleLabels_mem (i j k : ι) (b : Bool) (h : k = i ∨ k = j) :
    (lengthTwoTheta ι).simpleEdge nonloop (k, b) ∈
      (lengthTwoTheta ι).simpleLabels nonloop (selectedBranches i j) := by
  refine ⟨(k, b), ?_, rfl⟩
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Exact crossing control: selected labels are admitted by membership, and
an unselected arc cannot meet the sphere by the strict distance estimate. -/
theorem crossing_selectedBranches {i j : ι} (hij : i ≠ j) (a : ℝ) (ha : 0 < a) :
    (realization i j a).CrossingControlledBy
      (sphere (0 : ℝ × ℝ) (3 * a / 4))
      ((lengthTwoTheta ι).simpleLabels nonloop (selectedBranches i j)) := by
  intro u v huv hcross
  obtain ⟨t, ht⟩ := hcross
  cases u with
  | inl b =>
      cases v with
      | inl c =>
          exfalso
          obtain ⟨e, he⟩ := ((lengthTwoTheta ι).simpleGraph_adj_iff.mp huv).2
          rcases he with ⟨hs, ht'⟩ | ⟨hs, ht'⟩ <;> cases hs <;> cases ht'
      | inr k =>
          by_cases hki : k = i
          · subst k
            convert simpleLabels_mem i j i b (Or.inl rfl) using 1
            apply Subtype.ext
            rfl
          · by_cases hkj : k = j
            · subst k
              convert simpleLabels_mem i j j b (Or.inr rfl) using 1
              apply Subtype.ext
              rfl
            · exfalso
              have hle := dist_arc_le_of_ne hki hkj a ha.le b t
              change dist (branchArc i j a k b t) 0 = 3 * a / 4 at ht
              rw [ht] at hle
              linarith
  | inr k =>
      cases v with
      | inl b =>
          by_cases hki : k = i
          · subst k
            convert simpleLabels_mem i j i b (Or.inl rfl) using 1
            apply Subtype.ext
            exact Sym2.eq_swap
          · by_cases hkj : k = j
            · subst k
              convert simpleLabels_mem i j j b (Or.inr rfl) using 1
              apply Subtype.ext
              exact Sym2.eq_swap
            · exfalso
              have hle := dist_arc_le_of_ne hki hkj a ha.le b (unitInterval.symm t)
              change dist (branchArc i j a k b (unitInterval.symm t)) 0 =
                3 * a / 4 at ht
              rw [ht] at hle
              linarith
      | inr l =>
          exfalso
          obtain ⟨e, he⟩ := ((lengthTwoTheta ι).simpleGraph_adj_iff.mp huv).2
          rcases he with ⟨hs, ht'⟩ | ⟨hs, ht'⟩ <;> cases hs <;> cases ht'

lemma selectedConfig_open (i j : ι) :
    selectedBranches i j ⊆ (lengthTwoTheta ι).openEdgeSet (selectedConfig i j) := by
  intro e he
  change (lengthTwoTheta ι).setConfig (selectedBranches i j) e = true
  simp [LabelledMultigraph.setConfig, he]

lemma selectedConfig_closed_of_ne {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j)
    (b : Bool) : selectedConfig i j (k, b) = false := by
  simp [selectedConfig, selectedBranches, LabelledMultigraph.setConfig,
    branch, hki, hkj]

/-- The selected edges are an exact matroid circuit. -/
theorem isCircuit_selectedBranches [Nonempty ι] {i j : ι} (hij : i ≠ j) :
    (lengthTwoTheta ι).cycleMatroid.IsCircuit (selectedBranches i j) :=
  (isCircuit_iff_two_branches (selectedBranches i j)).mpr ⟨i, j, hij, rfl⟩

/-- The selected circuit is open and connected, and controls every crossing
of the separating sphere. -/
theorem sphericalOpenCircuit_selectedBranches [Nonempty ι] {i j : ι}
    (hij : i ≠ j) (a : ℝ) (ha : 0 < a) :
    SphericalOpenCircuit (realization i j a)
      ((lengthTwoTheta ι).simpleConfig nonloop (selectedConfig i j))
      ((lengthTwoTheta ι).simpleLabels nonloop (selectedBranches i j))
      0 (3 * a / 4) where
  radius_pos := by linarith
  crossing := crossing_selectedBranches hij a ha
  vertex_off := vertex_off_sphere i j a ha
  label_open := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := he
    exact (lengthTwoTheta ι).simpleConfig_simpleEdge_of_mem_openEdgeSet
      nonloop (selectedConfig_open i j) hf
  openConnected :=
    (lengthTwoTheta ι).openLabelConnected_simple_of_cycleMatroid_isCircuit
      nonloop (selectedConfig_open i j) (isCircuit_selectedBranches hij)

/-- Every selected straight segment actually crosses the sphere.  Together
with the inner-arc avoidance theorem, this makes the separating geometry
non-vacuous. -/
theorem exists_branchArc_crossing {i j k : ι} (hk : k = i ∨ k = j)
    (hij : i ≠ j) (a : ℝ) (ha : 0 < a) (b : Bool) :
    ∃ t : I, branchArc i j a k b t ∈ sphere (0 : ℝ × ℝ) (3 * a / 4) := by
  have hx : terminal a b ∈ ball (0 : ℝ × ℝ) (3 * a / 4) := by
    rw [Metric.mem_ball, dist_terminal a ha.le]
    linarith
  have hout : dist (internal i j a k) 0 = a := by
    rcases hk with hki | hkj
    · rw [hki]
      exact dist_internal_left i j a ha.le
    · rw [hkj]
      exact dist_internal_right hij a ha.le
  have hy : internal i j a k ∈
      (fun z : ℝ × ℝ => dist z 0) ⁻¹' Ioi (3 * a / 4) := by
    change 3 * a / 4 < dist (internal i j a k) 0
    rw [hout]
    linarith
  obtain ⟨t, ⟨htI, ht⟩, _⟩ := segmentArc_existsUnique_crossing hx hy
  refine ⟨⟨t, htI⟩, ?_⟩
  exact ht

/-- On a finite branch index the simple quotient is connected. -/
theorem preconnected_simpleGraph [Nonempty ι] :
    (lengthTwoTheta ι).simpleGraph.Preconnected := by
  let k₀ : ι := Classical.choice inferInstance
  have hadj (k : ι) (b : Bool) :
      (lengthTwoTheta ι).simpleGraph.Adj (Sum.inl b) (Sum.inr k) := by
    apply (lengthTwoTheta ι).simpleGraph_adj_iff.mpr
    refine ⟨by simp, (k, b), Or.inl ⟨rfl, rfl⟩⟩
  have hroot : ∀ v, (lengthTwoTheta ι).simpleGraph.Reachable v (Sum.inl false) := by
    intro v
    cases v with
    | inl b =>
        cases b
        · exact SimpleGraph.Reachable.refl _
        · exact (hadj k₀ true).reachable.trans
            ((hadj k₀ false).symm.reachable)
    | inr k => exact (hadj k false).symm.reachable
  intro u v
  exact (hroot u).trans (hroot v).symm

/-- Properness is immediate but explicit for this finite window: every metric
ball has only finitely many vertex preimages. -/
theorem finite_vertex_preimage_ball (i j : ι) (a r : ℝ) :
    (vertex i j a ⁻¹' ball (0 : ℝ × ℝ) r).Finite :=
  Set.finite_univ.subset (Set.subset_univ _)

/-- Exact plane-dual certificate and selected spherical circuit on the same
generalized theta window.  This is a finite window theorem, not an
infinite-volume or dual-nonpercolation assertion. -/
theorem planeDual_sphericalWindow (G : LabelledMultigraph)
    (hG : G.IsLabelledCycle) {i j : G.Edge} (hij : i ≠ j) (a : ℝ) (ha : 0 < a) :
    (lengthTwoThetaPair G).GraphicDualCertificate ∧
      SphericalOpenCircuit (realization i j a)
        ((lengthTwoTheta G.Edge).simpleConfig nonloop (selectedConfig i j))
        ((lengthTwoTheta G.Edge).simpleLabels nonloop (selectedBranches i j))
        0 (3 * a / 4) := by
  letI : Nonempty G.Edge := LabelledDualPair.cycle_nonempty_edge G hG
  exact ⟨lengthTwoThetaPair_graphicDualCertificate G hG,
    sphericalOpenCircuit_selectedBranches hij a ha⟩

/-- A third branch witnesses that the selected configuration is not all-open. -/
theorem selectedConfig_ne_allOpen_of_ne {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j)
    (b : Bool) : selectedConfig i j ≠ (lengthTwoTheta ι).allOpen := by
  intro h
  have heq := congrFun h (k, b)
  rw [selectedConfig_closed_of_ne hki hkj b] at heq
  exact Bool.false_ne_true heq

namespace ConcreteTriangle

/-- A three-edge, three-vertex cycle obtained by one facial subdivision of
the two-edge cycle. -/
noncomputable abbrev triangleGraph : LabelledMultigraph :=
  (LabelledDualPair.subdivPair
    (LabelledDualPair.cyclePair twoEdgeCycle) false).primal

/-- The graph-theoretic cycle certificate is transported through the actual
subdivision; no new matroid-duality premise is used. -/
theorem isLabelledCycle_triangleGraph : triangleGraph.IsLabelledCycle := by
  let P : LabelledDualPair := LabelledDualPair.cyclePair twoEdgeCycle
  have hP : P.primal.IsLabelledCycle := isLabelledCycle_twoEdgeCycle
  have hproject : LabelledDualPair.projectConfig P false
      triangleGraph.allOpen = P.primal.allOpen := by
    funext b
    cases b <;>
      simp [P, LabelledDualPair.projectConfig, LabelledMultigraph.allOpen,
        triangleGraph, LabelledDualPair.subdivPair]
  have hlift (u v : P.Vertex) : triangleGraph.connectionGraph
      triangleGraph.freeBoundary triangleGraph.allOpen |>.Reachable (some u) (some v) := by
    apply LabelledDualPair.reachable_some_of_projected P false triangleGraph.allOpen
    rw [hproject]
    exact hP.preconnected u v
  have hnone : triangleGraph.connectionGraph triangleGraph.freeBoundary
      triangleGraph.allOpen |>.Reachable none
        (some (LabelledDualPair.collapse P false triangleGraph.allOpen none)) := by
    exact LabelledDualPair.reachable_none_collapse P false triangleGraph.allOpen
      (Or.inl rfl)
  refine ⟨⟨some false⟩, by rfl, ?_, ?_⟩
  · intro u v
    cases u with
    | none =>
        cases v with
        | none => exact SimpleGraph.Reachable.refl _
        | some b => exact hnone.trans (hlift _ b)
    | some a =>
        cases v with
        | none => exact (hlift a _).trans hnone.symm
        | some b => exact hlift a b
  · intro ω hω
    apply (LabelledDualPair.primal_isOpenForest_iff P false ω).mpr
    apply hP.isOpenForest_of_ne_allOpen
    intro hp
    apply hω
    have hfalse : ω (some false) = true ∧ ω none = true := by
      have h := congrFun hp false
      dsimp [P, LabelledDualPair.projectConfig, LabelledMultigraph.allOpen] at h
      split at h
      · exact Bool.and_eq_true_iff.mp h
      · rename_i hne
        exact (hne rfl).elim
    have htrue : ω (some true) = true := by
      have h := congrFun hp true
      dsimp [P, LabelledDualPair.projectConfig, LabelledMultigraph.allOpen] at h
      rw [ite_eq_right (by intro h'; cases h')] at h
      exact h
    funext x
    cases x with
    | none => exact hfalse.2
    | some b =>
        cases b
        · exact hfalse.1
        · exact htrue

/-- The three explicit branch indices. -/
def outerLeft : triangleGraph.Edge := some false
def outerRight : triangleGraph.Edge := some true
def inner : triangleGraph.Edge := none

lemma inner_ne_outerLeft : inner ≠ outerLeft := by
  intro h
  change (none : Option Bool) = some false at h
  cases h
lemma inner_ne_outerRight : inner ≠ outerRight := by
  intro h
  change (none : Option Bool) = some true at h
  cases h
lemma outerLeft_ne_outerRight : outerLeft ≠ outerRight := by
  intro h
  change (some false : Option Bool) = some true at h
  have hb : (false : Bool) = true := Option.some.inj h
  cases hb

/-- One fully explicit connected, non-all-open, three-branch plane-dual
spherical window. -/
theorem planeDual_sphericalWindow (a : ℝ) (ha : 0 < a) :
    (lengthTwoThetaPair triangleGraph).GraphicDualCertificate ∧
      (lengthTwoTheta triangleGraph.Edge).simpleGraph.Preconnected ∧
      selectedConfig outerLeft outerRight ≠
        (lengthTwoTheta triangleGraph.Edge).allOpen ∧
      SphericalOpenCircuit (realization outerLeft outerRight a)
        ((lengthTwoTheta triangleGraph.Edge).simpleConfig nonloop
          (selectedConfig outerLeft outerRight))
        ((lengthTwoTheta triangleGraph.Edge).simpleLabels nonloop
          (selectedBranches outerLeft outerRight)) 0 (3 * a / 4) := by
  letI : Nonempty triangleGraph.Edge := ⟨outerLeft⟩
  refine ⟨lengthTwoThetaPair_graphicDualCertificate triangleGraph
      isLabelledCycle_triangleGraph,
    preconnected_simpleGraph,
    selectedConfig_ne_allOpen_of_ne inner_ne_outerLeft inner_ne_outerRight false,
    sphericalOpenCircuit_selectedBranches outerLeft_ne_outerRight a ha⟩

/-- The explicit inner branch is closed in the same configuration. -/
theorem inner_closed (b : Bool) : selectedConfig outerLeft outerRight (inner, b) = false :=
  selectedConfig_closed_of_ne inner_ne_outerLeft inner_ne_outerRight b

end ConcreteTriangle

end
end FK.PlaneTopology.GeneralizedThetaWindow

#print axioms FK.PlaneTopology.GeneralizedThetaWindow.ConcreteTriangle.isLabelledCycle_triangleGraph
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.ConcreteTriangle.planeDual_sphericalWindow
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.crossing_selectedBranches
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.sphericalOpenCircuit_selectedBranches
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.exists_branchArc_crossing
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.preconnected_simpleGraph
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.finite_vertex_preimage_ball
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.selectedConfig_ne_allOpen_of_ne
#print axioms FK.PlaneTopology.GeneralizedThetaWindow.planeDual_sphericalWindow
