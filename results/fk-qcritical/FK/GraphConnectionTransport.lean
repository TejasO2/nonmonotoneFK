import FK.MovingDominatedRate
import FK.GrowingFamilyDLR
import FK.ClusterEscape

/-! Connections of a finite graph box as paths in the global wired graph. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport

universe u v

variable {V : Type u} [Countable V] {G : SimpleGraph V} {E : Type v}

/-- Close every global edge outside a finite box. -/
noncomputable def closeOutside (B : FiniteBox G.edgeSet) (ω : G.edgeSet → Bool) : G.edgeSet → Bool :=
  fun e => if e ∈ B.edges then ω e else false

@[simp] lemma closeOutside_apply_of_mem (B : FiniteBox G.edgeSet) (ω : G.edgeSet → Bool)
    {e : G.edgeSet} (he : e ∈ B.edges) : closeOutside B ω e = ω e := by
  simp [closeOutside, he]

@[simp] lemma closeOutside_apply_of_notMem (B : FiniteBox G.edgeSet) (ω : G.edgeSet → Bool)
    {e : G.edgeSet} (he : e ∉ B.edges) : closeOutside B ω e = false := by
  simp [closeOutside, he]

/-- Extend a finite-box boundary partition to the global vertex type.  Outside
vertices have only their reflexive class; injectivity of the box embedding makes
this a setoid. -/
def globalBoundary {B : FiniteBox G.edgeSet} (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (hinj : Function.Injective (data.vertex 0)) (α : B.BoundaryPartition) : Setoid V where
  r x y := (∃ a b, x = data.vertex 0 a ∧ y = data.vertex 0 b ∧ α.r a b) ∨ x = y
  iseqv := by
    refine ⟨fun x => Or.inr rfl, ?_, ?_⟩
    · intro x y h
      rcases h with ⟨a, b, rfl, rfl, hab⟩ | rfl
      · exact Or.inl ⟨b, a, rfl, rfl, α.symm hab⟩
      · exact Or.inr rfl
    · intro x y z hxy hyz
      rcases hxy with ⟨a, b, rfl, rfl, hab⟩ | rfl
      · rcases hyz with ⟨c, d, hcy, hdz, hcd⟩ | heq
        · have hbc : b = c := hinj hcy
          subst c
          exact Or.inl ⟨a, d, rfl, hdz, α.trans hab hcd⟩
        · exact Or.inl ⟨a, b, rfl, heq.symm, hab⟩
      · exact hyz

lemma globalBoundary_rel {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (hinj : Function.Injective (data.vertex 0)) (α : B.BoundaryPartition) (x y : B.Vertex) :
    (globalBoundary data hinj α).r (data.vertex 0 x) (data.vertex 0 y) ↔ α.r x y := by
  constructor
  · rintro (⟨a, b, hx, hy, hab⟩ | heq)
    · have hxa : a = x := hinj hx.symm
      have hyb : b = y := hinj hy.symm
      simpa [hxa, hyb] using hab
    · have hxy : x = y := hinj heq
      exact hxy ▸ α.refl' x
  · intro h
    exact Or.inl ⟨x, y, rfl, rfl, h⟩

lemma globalBoundary_mem_range {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (hinj : Function.Injective (data.vertex 0)) (α : B.BoundaryPartition) {x y : V}
    (h : (globalBoundary data hinj α).r x y) : x ∈ Set.range (data.vertex 0) →
      y ∈ Set.range (data.vertex 0) := by
  rintro ⟨a, ha⟩
  rcases h with ⟨c, d, hxc, hyd, hcd⟩ | rfl
  · exact ⟨d, hyd.symm⟩
  · exact ⟨a, ha⟩

section BoxConnection

variable {B : FiniteBox G.edgeSet}
variable (data : SimpleGraphBoxData G (fun _ : ℕ => B))
variable (hinj : Function.Injective (data.vertex 0))

lemma mem_range_wired_step (α : B.BoundaryPartition) (ω : G.edgeSet → Bool)
    {x y : V} (hxy : (ClusterEscape.wiredGraph G (globalBoundary data hinj α)
      (closeOutside B ω)).Adj x y) :
    x ∈ Set.range (data.vertex 0) → y ∈ Set.range (data.vertex 0) := by
  intro hx
  rcases hxy.2 with hbd | ⟨e, heopen, heq⟩
  · exact globalBoundary_mem_range data hinj α hbd hx
  · have hemem : e ∈ B.edges := by
      by_contra hn
      rw [closeOutside_apply_of_notMem B ω hn] at heopen
      simp at heopen
    let eB : B.edges := ⟨e, hemem⟩
    have heq' : s(data.vertex 0 (B.source eB), data.vertex 0 (B.target eB)) = s(x, y) := by
      rw [data.endpoint 0 eB, heq]
    rw [Sym2.eq_iff] at heq'
    rcases heq' with heqxy | heqyx
    · exact ⟨B.target eB, heqxy.2⟩
    · exact ⟨B.source eB, heqyx.1⟩

lemma mem_range_of_wired_walk (α : B.BoundaryPartition) (ω : G.edgeSet → Bool)
    {x y : V} (p : (ClusterEscape.wiredGraph G (globalBoundary data hinj α)
      (closeOutside B ω)).Walk x y) :
    x ∈ Set.range (data.vertex 0) → y ∈ Set.range (data.vertex 0) := by
  induction p with
  | nil => exact id
  | @cons a b c hab p ih =>
      intro ha
      exact ih (mem_range_wired_step data hinj α ω hab ha)

/-- The finite box connection graph is exactly the global wired graph after
closing all edges outside the box. -/
theorem reachable_wiredGraph_closeOutside_iff (α : B.BoundaryPartition) (ω : G.edgeSet → Bool)
    (x y : B.Vertex) :
    (ClusterEscape.wiredGraph G (globalBoundary data hinj α) (closeOutside B ω)).Reachable
        (data.vertex 0 x) (data.vertex 0 y) ↔
      (B.graph.connectionGraph α (fun e => ω e.1)).Reachable x y := by
  constructor
  · intro h
    obtain ⟨p⟩ := h
    have go : ∀ {a b : V} (p : (ClusterEscape.wiredGraph G (globalBoundary data hinj α)
        (closeOutside B ω)).Walk a b), ∀ {x y : B.Vertex},
        data.vertex 0 x = a → data.vertex 0 y = b →
          (B.graph.connectionGraph α (fun e => ω e.1)).Reachable x y := by
      intro a b p
      induction p with
      | nil =>
          intro x y hx hy
          have hxy : x = y := (hinj (hy.trans hx.symm)).symm
          subst y
          exact SimpleGraph.Reachable.refl _
      | @cons a b c hab p ih =>
          intro x y hx hy
          have ha : a ∈ Set.range (data.vertex 0) := ⟨x, hx⟩
          have hb : b ∈ Set.range (data.vertex 0) :=
            mem_range_wired_step data hinj α ω hab ha
          obtain ⟨b', hb'⟩ := hb
          subst a
          subst b
          have hstep : (B.graph.connectionGraph α (fun e => ω e.1)).Adj x b' := by
            refine ⟨fun heq => hab.1 (congrArg (data.vertex 0) heq), ?_⟩
            rcases hab.2 with hbd | ⟨e, heopen, heq⟩
            · exact Or.inl ((globalBoundary_rel data hinj α x b').mp hbd)
            · apply Or.inr
              have hemem : e ∈ B.edges := by
                by_contra hn
                rw [closeOutside_apply_of_notMem B ω hn] at heopen
                simp at heopen
              let eB : B.edges := ⟨e, hemem⟩
              have heopenB : (fun e : B.edges => ω e.1) eB = true := by
                change ω e = true
                rw [← closeOutside_apply_of_mem B ω hemem]
                exact heopen
              refine ⟨eB, heopenB, ?_⟩
              have heq' : s(data.vertex 0 (B.source eB), data.vertex 0 (B.target eB)) =
                  s(data.vertex 0 x, data.vertex 0 b') := by
                rw [data.endpoint 0 eB, heq]
              rw [Sym2.eq_iff] at heq'
              rcases heq' with h1 | h2
              · exact Or.inl ⟨hinj h1.1, hinj h1.2⟩
              · exact Or.inr ⟨hinj h2.1, hinj h2.2⟩
          exact hstep.reachable.trans (ih rfl hy)
    exact go p rfl rfl
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c hxy hstep ih =>
        refine ih.trans (SimpleGraph.Adj.reachable ?_)
        refine ⟨fun heq => hstep.1 (hinj heq), ?_⟩
        rcases hstep.2 with hbd | ⟨e, heopen, hjoin⟩
        · exact Or.inl ((globalBoundary_rel data hinj α _ _).mpr hbd)
        · apply Or.inr
          refine ⟨e.1, ?_, ?_⟩
          · rw [closeOutside_apply_of_mem B ω e.2]
            exact heopen
          · rw [← data.endpoint 0 e]
            change s(data.vertex 0 (B.graph.source e), data.vertex 0 (B.graph.target e)) = _
            rcases hjoin with h | h
            · rw [h.1, h.2]
            · rw [h.1, h.2, Sym2.eq_swap]


lemma globalBoundary_bot {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (hinj : Function.Injective (data.vertex 0)) :
    globalBoundary data hinj (⊥ : B.BoundaryPartition) = ⊥ := by
  apply Setoid.ext
  intro x y
  constructor
  · rintro (⟨a, b, rfl, rfl, hab⟩ | heq)
    · have h : a = b := hab
      subst b
      rfl
    · exact heq
  · intro heq
    exact Or.inr heq

/-- With no boundary wiring, `wiredGraph` connection is ordinary open connection. -/
theorem reachable_wiredGraph_bot_iff_openConnected (ω : G.edgeSet → Bool) (x y : V) :
    (ClusterEscape.wiredGraph G (⊥ : Setoid V) ω).Reachable x y ↔
      OpenConnected G ω Set.univ x y := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact OpenConnected.refl ω Set.univ _
    | @tail b c hxy hstep ih =>
        refine ih.trans ?_
        rcases hstep.2 with hbd | ⟨e, heopen, heq⟩
        · exact (hstep.1 hbd).elim
        · have hadj := (SimpleGraph.mem_edgeSet G).mp (show s(_, _) ∈ G.edgeSet from by
            rw [← heq]
            exact e.2)
          exact OpenConnected.of_adj hadj (Set.mem_univ _) (by
            rw [show (⟨_, hadj⟩ : G.edgeSet) = e from Subtype.ext heq.symm]
            exact heopen)
  · rintro ⟨p, hp⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w hadj p ih =>
        rw [isOpenIn_cons] at hp
        have hstep : (ClusterEscape.wiredGraph G (⊥ : Setoid V) ω).Adj u v := by
          refine ⟨hadj.ne, Or.inr ⟨(⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ : G.edgeSet),
            hp.1.2, rfl⟩⟩
        exact hstep.reachable.trans (ih hp.2)

/-- Closing only the box interior gives smaller configurations than closing
only the exterior. -/
lemma closeInside_le_config (B : FiniteBox G.edgeSet) (ω : G.edgeSet → Bool) :
    closeInside B (FKLimit.exteriorRestriction B.edges ω) ≤ ω := by
  intro e
  by_cases he : e ∈ B.edges
  · simp [closeInside, FiniteBox.glue, he, closeOutside]
  · simp [closeInside, FiniteBox.glue, he, closeOutside, FKLimit.exteriorRestriction]

lemma wiredGraph_components_reachable_iff_openConnected {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (hinj : Function.Injective (data.vertex 0)) (ω : G.edgeSet → Bool) (x y : B.Vertex) :
    (ClusterEscape.wiredGraph G
      (globalBoundary data hinj (data.geometry.components 0
        (FKLimit.exteriorRestriction B.edges ω))) (ω)).Reachable
        (data.vertex 0 x) (data.vertex 0 y) ↔
      OpenConnected G (ω) Set.univ (data.vertex 0 x) (data.vertex 0 y) := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    have go : ∀ {a b : V}, Relation.ReflTransGen
        (ClusterEscape.wiredGraph G
          (globalBoundary data hinj (data.geometry.components 0
            (FKLimit.exteriorRestriction B.edges ω))) (ω)).Adj a b →
        OpenConnected G (ω) Set.univ a b := by
      intro a b h
      induction h with
      | refl => exact OpenConnected.refl _ Set.univ _
      | @tail b c hxy hstep ih =>
          refine ih.trans ?_
          rcases hstep.2 with hbd | ⟨e, heopen, heq⟩
          · rcases hbd with ⟨u, v, hbu, hcv, hopen⟩ | heq
            · subst b
              subst c
              exact OpenConnected.mono_config hopen (closeInside_le_config B ω)
            · subst c
              exact OpenConnected.refl _ Set.univ _
          · have hadj := (SimpleGraph.mem_edgeSet G).mp (show s(_, _) ∈ G.edgeSet from by
              rw [← heq]
              exact e.2)
            exact OpenConnected.of_adj hadj (Set.mem_univ _) (by
              rw [show (⟨_, hadj⟩ : G.edgeSet) = e from Subtype.ext heq.symm]
              exact heopen)
    exact go h
  · rintro ⟨p, hp⟩
    have go : ∀ {a b : V} (p : G.Walk a b), IsOpenIn (ω) Set.univ p →
        (ClusterEscape.wiredGraph G
          (globalBoundary data hinj (data.geometry.components 0
            (FKLimit.exteriorRestriction B.edges ω))) (ω)).Reachable a b := by
      intro a b p
      induction p with
      | nil =>
          intro hp
          exact SimpleGraph.Reachable.refl _
      | @cons u v w hadj p ih =>
          intro hp
          rw [isOpenIn_cons] at hp
          have hstep : (ClusterEscape.wiredGraph G
            (globalBoundary data hinj (data.geometry.components 0
              (FKLimit.exteriorRestriction B.edges ω))) (ω)).Adj u v := by
            refine ⟨hadj.ne, Or.inr ⟨(⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ : G.edgeSet),
              hp.1.2, rfl⟩⟩
          exact hstep.reachable.trans (ih hp.2)
    exact go p hp


/-- Global wired paths between box vertices compress to the canonical free
finite-box connection graph. -/
theorem reachable_wiredGraph_components_iff_freeComponents {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (hinj : Function.Injective (data.vertex 0)) (ω : G.edgeSet → Bool) (x y : B.Vertex) :
    (ClusterEscape.wiredGraph G
      (globalBoundary data hinj (data.geometry.components 0
        (FKLimit.exteriorRestriction B.edges ω))) (ω)).Reachable
        (data.vertex 0 x) (data.vertex 0 y) ↔
      (B.graph.connectionGraph
        (data.free.partition 0 (FKLimit.exteriorRestriction B.edges ω))
        (fun e => ω e.1)).Reachable x y := by
  let ξ : B.BoundaryPartition := data.geometry.components 0
    (FKLimit.exteriorRestriction B.edges ω)
  let γ : Setoid V := globalBoundary data hinj ξ
  change (ClusterEscape.wiredGraph G γ ω).Reachable (data.vertex 0 x) (data.vertex 0 y) ↔
    (B.graph.connectionGraph ξ (fun e => ω e.1)).Reachable x y
  have key : ∀ x : B.Vertex, ∀ {z : V},
      (ClusterEscape.wiredGraph G γ ω).Reachable (data.vertex 0 x) z →
      ∃ w : B.Vertex, (B.graph.connectionGraph ξ (fun e => ω e.1)).Reachable x w ∧
        OpenConnected G (closeInside B
          (FKLimit.exteriorRestriction B.edges ω)) Set.univ z (data.vertex 0 w) := by
    intro x z h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl =>
        exact ⟨x, SimpleGraph.Reachable.refl _, OpenConnected.refl _ Set.univ _⟩
    | @tail u v huv hstep ih =>
        obtain ⟨w, hw, hAw⟩ := ih
        rcases hstep.2 with hbd | ⟨e, heopen, heq⟩
        · have hA : OpenConnected G (closeInside B
              (FKLimit.exteriorRestriction B.edges ω)) Set.univ u v := by
            rcases hbd with ⟨a, b, hua, hvb, hr⟩ | heq
            · subst u
              subst v
              exact hr
            · subst v
              exact OpenConnected.refl _ Set.univ _
          exact ⟨w, hw, (FK.InfiniteVolume.ConventionGeometry.openConnected_symm hA).trans hAw⟩
        · by_cases heB : e ∈ B.edges
          · have hrange : u ∈ Set.range (data.vertex 0) ∧ v ∈ Set.range (data.vertex 0) := by
              have heq' : s(data.vertex 0 (B.source ⟨e, heB⟩),
                  data.vertex 0 (B.target ⟨e, heB⟩)) = s(u, v) := by
                rw [data.endpoint 0 ⟨e, heB⟩, heq]
              rw [Sym2.eq_iff] at heq'
              rcases heq' with h | h
              · exact ⟨⟨B.source ⟨e, heB⟩, h.1⟩, ⟨B.target ⟨e, heB⟩, h.2⟩⟩
              · exact ⟨⟨B.target ⟨e, heB⟩, h.2⟩, ⟨B.source ⟨e, heB⟩, h.1⟩⟩
            obtain ⟨u', hu'⟩ := hrange.1
            obtain ⟨v', hv'⟩ := hrange.2
            have hjoin : B.graph.Joins ⟨e, heB⟩ u' v' := by
              have heq' : s(data.vertex 0 (B.source ⟨e, heB⟩),
                  data.vertex 0 (B.target ⟨e, heB⟩)) = s(u, v) := by
                rw [data.endpoint 0 ⟨e, heB⟩, heq]
              rw [Sym2.eq_iff] at heq'
              rcases heq' with h | h
              · apply Or.inl
                constructor
                · apply hinj
                  rw [hu', h.1]
                · apply hinj
                  rw [hv', h.2]
              · apply Or.inr
                constructor
                · apply hinj
                  rw [hv', h.1]
                · apply hinj
                  rw [hu', h.2]
            have hstep' : (B.graph.connectionGraph ξ (fun e => ω e.1)).Adj u' v' := by
              refine ⟨?_, Or.inr ⟨⟨e, heB⟩, heopen, hjoin⟩⟩
              intro heq''
              apply hstep.1
              exact hu'.symm.trans ((congrArg (data.vertex 0) heq'').trans hv')
            have hzw : ξ.r u' w := by
              change OpenConnected G (closeInside B
                (FKLimit.exteriorRestriction B.edges ω)) Set.univ (data.vertex 0 u') (data.vertex 0 w)
              rw [hu']
              exact hAw
            subst v
            have hpath : (B.graph.connectionGraph ξ (fun e => ω e.1)).Reachable x v' := by
              by_cases hwu : w = u'
              · subst w
                exact hw.trans hstep'.reachable
              · have hstepW : (B.graph.connectionGraph ξ (fun e => ω e.1)).Adj w u' := by
                  exact ⟨hwu, Or.inl (ξ.symm hzw)⟩
                exact hw.trans (hstepW.reachable.trans hstep'.reachable)
            exact ⟨v', hpath, OpenConnected.refl _ Set.univ _⟩
          · have hA : OpenConnected G (closeInside B
                (FKLimit.exteriorRestriction B.edges ω)) Set.univ u v := by
              have hadj : G.Adj u v := by
                rw [← SimpleGraph.mem_edgeSet, ← heq]
                exact e.2
              have heqEdge : e = (⟨s(u, v), hadj⟩ : G.edgeSet) := Subtype.ext heq
              have heB' : (⟨s(u, v), hadj⟩ : G.edgeSet) ∉ B.edges := by
                intro hmem
                apply heB
                rw [← heqEdge] at hmem
                exact hmem
              have hclose : (closeInside B
                  (FKLimit.exteriorRestriction B.edges ω)) (⟨s(u, v), hadj⟩ : G.edgeSet) = true := by
                simp only [closeInside, FiniteBox.glue, heB', FKLimit.exteriorRestriction,
                  dite_false]
                simpa only [heqEdge] using heopen
              exact OpenConnected.of_adj hadj (Set.mem_univ _) hclose
            exact ⟨w, hw, (FK.InfiniteVolume.ConventionGeometry.openConnected_symm hA).trans hAw⟩
  constructor
  · intro h
    obtain ⟨w, hw, hAw⟩ := key x h
    by_cases hwy : w = y
    · subst w
      exact hw
    · refine hw.trans (SimpleGraph.Adj.reachable ⟨hwy, Or.inl ?_⟩)
      exact ξ.symm hAw
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail u v huv hstep ih =>
        refine ih.trans (SimpleGraph.Adj.reachable ?_)
        refine ⟨fun heq => hstep.1 (hinj heq), ?_⟩
        rcases hstep.2 with hbd | ⟨e, heopen, hjoin⟩
        · exact Or.inl ((globalBoundary_rel data hinj ξ _ _).mpr hbd)
        · apply Or.inr
          refine ⟨e.1, heopen, ?_⟩
          rw [← data.endpoint 0 e]
          change s(data.vertex 0 (B.graph.source e), data.vertex 0 (B.graph.target e)) = _
          rcases hjoin with h | h
          · rw [h.1, h.2]
          · rw [h.1, h.2, Sym2.eq_swap]



/-- Ordinary global open connection between box vertices is exactly the
canonical free finite-box connection event. -/
theorem openConnected_iff_freeComponents {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (hinj : Function.Injective (data.vertex 0)) (ω : G.edgeSet → Bool) (x y : B.Vertex) :
    OpenConnected G ω Set.univ (data.vertex 0 x) (data.vertex 0 y) ↔
      (B.graph.connectionGraph
        (data.free.partition 0 (FKLimit.exteriorRestriction B.edges ω))
        (fun e => ω e.1)).Reachable x y := by
  rw [← wiredGraph_components_reachable_iff_openConnected data hinj ω x y]
  exact reachable_wiredGraph_components_iff_freeComponents data hinj ω x y




end BoxConnection

end FK.NestedFinDLR
