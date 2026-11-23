import FK.StarBoundaryCutset

/-!
# Finite-box cycle paths for active-device enhancements

Separated global cycles provide the path certificates required by the active
cycle-device comparison.  The complementary walk is constructed inside the
original cycle, then lifted to a compatible finite labelled box.  Separation
makes its auxiliary labels avoid every other active enhanced pivot.  No special
boundary partition is needed: arbitrary boundary wiring can only add connections.

Vertex-map injectivity is an explicit hypothesis of the finite-box lift.
-/

open Set
open scoped SimpleGraph Sym2 Classical BigOperators

namespace FK.QuasiTransitive

/-- A cycle containing an edge has an explicit complementary walk between the
edge's endpoints.  Every edge of the complementary walk is an edge of the
original cycle other than the distinguished edge. -/
theorem exists_alternateWalk_of_mem_cycle {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {x v w : V} (c : G.Walk x x) (hc : c.IsCycle)
    {e : G.edgeSet} (he : (e : Sym2 V) ∈ c.edges) (hevw : (e : Sym2 V) = s(v, w)) :
    ∃ p : G.Walk v w, ∀ f : G.edgeSet, (f : Sym2 V) ∈ p.edges →
      (f : Sym2 V) ∈ c.edges ∧ f ≠ e := by
  classical
  have hvE : v ∈ (e : Sym2 V) := by rw [hevw]; simp
  have hv : v ∈ c.support := c.mem_support_of_mem_edges he hvE
  let c' : G.Walk v v := c.rotate v hv
  have hc' : c'.IsCycle := by
    exact hc.rotate hv
  have he' : (e : Sym2 V) ∈ c'.edges := by
    exact (c.rotate_edges v hv).mem_iff.mpr he
  have hc'mem : ∀ {a : Sym2 V}, a ∈ c'.edges → a ∈ c.edges := by
    intro a ha
    exact (c.rotate_edges v hv).mem_iff.mp ha
  cases hcc' : c' with
  | nil =>
      rw [hcc'] at hc'
      exact (SimpleGraph.Walk.not_isCycle_nil hc').elim
  | @cons _ z _ h p =>
      rw [hcc'] at hc' he' hc'mem
      by_cases hhead : s(v, z) = (e : Sym2 V)
      · have hzw : z = w := by
          have hpairs : s(v, z) = s(v, w) := hhead.trans hevw
          rcases Sym2.eq_iff.mp hpairs with hpair | hpair
          · exact hpair.2
          · exact (h.ne hpair.2.symm).elim
        subst z
        refine ⟨p.reverse, fun f hf => ?_⟩
        have hfp : (f : Sym2 V) ∈ p.edges := by
          simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hf
        refine ⟨hc'mem (by simp only [SimpleGraph.Walk.edges_cons, List.mem_cons,
          hfp, or_true]), ?_⟩
        intro hfe
        subst f
        have hnot := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc' |>.2
        have hnot' : (e : Sym2 V) ∉ p.edges := by
          simpa only [← hhead] using hnot
        exact hnot' hfp
      · have heList := he'
        rw [SimpleGraph.Walk.edges_cons] at heList
        have hep : (e : Sym2 V) ∈ p.edges := by
          rcases List.mem_cons.mp heList with hh | hh
          · exact (hhead hh.symm).elim
          · exact hh
        have hpc := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc'
        have hevw_p : s(v, w) ∈ p.edges := by rwa [← hevw]
        have hpen : w = p.penultimate := hpc.1.eq_penultimate_of_mem_edges hevw_p
        have hq : ∃ q : G.Walk v w, q.edges = s(v, z) :: p.dropLast.edges := by
          rw [hpen]
          exact ⟨SimpleGraph.Walk.cons h p.dropLast, rfl⟩
        obtain ⟨q, hqedges⟩ := hq
        have hnil : p.edges ≠ [] := List.ne_nil_of_mem hep
        have hlast : p.edges.getLast hnil = (e : Sym2 V) := by
          calc
            p.edges.getLast hnil = s(p.penultimate, v) :=
              SimpleGraph.Walk.getLast_edges_eq_mk_penultimate_end hnil
            _ = s(w, v) := by rw [← hpen]
            _ = s(v, w) := Sym2.eq_swap
            _ = (e : Sym2 V) := hevw.symm
        have hnotlast : (e : Sym2 V) ∉ p.edges.dropLast := by
          intro hed
          have hlastmem : p.edges.getLast hnil ∈ p.edges.dropLast := by
            rwa [hlast]
          have heq := List.Nodup.eq_of_getLast_mem_of_prefix
            (List.dropLast_prefix p.edges) hlastmem hpc.1.edges_nodup
          have hlen := congrArg List.length heq
          have hpos : 0 < p.edges.length := List.length_pos_iff.mpr hnil
          simp only [List.length_dropLast] at hlen
          omega
        refine ⟨q, fun f hf => ?_⟩
        rw [hqedges, List.mem_cons] at hf
        rcases hf with hfh | hft
        · have hfc : (f : Sym2 V) ∈ (SimpleGraph.Walk.cons h p).edges := by
            rw [SimpleGraph.Walk.edges_cons]
            exact List.mem_cons.mpr (Or.inl hfh)
          refine ⟨hc'mem hfc, ?_⟩
          intro hfe
          subst f
          exact hhead hfh.symm
        · have hft' : (f : Sym2 V) ∈ p.edges.dropLast := by
            simpa only [SimpleGraph.Walk.edges_dropLast] using hft
          have hfp : (f : Sym2 V) ∈ p.edges := List.mem_of_mem_dropLast hft'
          have hfc : (f : Sym2 V) ∈ (SimpleGraph.Walk.cons h p).edges := by
            rw [SimpleGraph.Walk.edges_cons]
            exact List.mem_cons.mpr (Or.inr hfp)
          refine ⟨hc'mem hfc, ?_⟩
          intro hfe
          subst f
          exact hnotlast hft'

end FK.QuasiTransitive

namespace FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData

open FK.Finite.LabelledMultigraph
open FK.Finite.Conditional
open FK.FiniteFiber

/-- The simple graph on box vertices whose adjacencies are witnessed by a
labelled box edge.  It is presented as the free all-open connection graph so
that its walks immediately give connection-event proofs under any wiring. -/
def underlyingGraph {E : Type*} (B : FK.InfiniteVolume.FiniteBox E) :
    SimpleGraph B.Vertex :=
  B.graph.connectionGraph B.graph.freeBoundary B.graph.allOpen

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FK.InfiniteVolume.FiniteBox G.edgeSet}

/-- Every labelled box edge gives an adjacency in the underlying simple graph. -/
lemma underlyingGraph_adj_source_target (data : SimpleGraphBoxData G box)
    (n : ℕ) (a : (box n).edges) :
    (underlyingGraph (box n)).Adj ((box n).source a) ((box n).target a) := by
  refine ⟨data.source_ne_target n a, Or.inr ⟨a, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Lift a global walk whose labels all belong to a box to a walk in that box.
Injectivity of the vertex map is exactly what lets successive lifted edges be
joined without adding any non-graph identification. -/
lemma exists_underlyingWalk (data : SimpleGraphBoxData G box) (n : ℕ)
    (hinj : Function.Injective (data.vertex n)) {u v : V} (p : G.Walk u v) :
    (∀ f : G.edgeSet, (f : Sym2 V) ∈ p.edges → f ∈ (box n).edges) →
    ∀ x : (box n).Vertex, data.vertex n x = u →
      ∃ y : (box n).Vertex, data.vertex n y = v ∧
        ∃ q : (underlyingGraph (box n)).Walk x y,
          ∀ a : (box n).edges,
            s((box n).source a, (box n).target a) ∈ q.edges →
              (a.1 : Sym2 V) ∈ p.edges := by
  induction p with
  | nil =>
      intro _ x hx
      refine ⟨x, hx, SimpleGraph.Walk.nil, ?_⟩
      intro a ha
      simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at ha
  | @cons u w v h p ih =>
      intro hp x hx
      let f : G.edgeSet := ⟨s(u, w), h⟩
      have hf : f ∈ (box n).edges := by
        apply hp f
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl rfl
      let a : (box n).edges := ⟨f, hf⟩
      have hend : s(data.vertex n ((box n).source a),
          data.vertex n ((box n).target a)) = s(u, w) := by
        simpa only [a, f] using data.endpoint n a
      obtain ⟨y, hy, hadj, hxy⟩ : ∃ y : (box n).Vertex, data.vertex n y = w ∧
          (underlyingGraph (box n)).Adj x y ∧
          s(x, y) = s((box n).source a, (box n).target a) := by
        rcases Sym2.eq_iff.mp hend with hst | hst
        · have hsax : (box n).source a = x := hinj (hst.1.trans hx.symm)
          refine ⟨(box n).target a, hst.2, ?_, ?_⟩
          · rw [← hsax]
            exact data.underlyingGraph_adj_source_target n a
          · rw [← hsax]
        · have htax : (box n).target a = x := hinj (hst.2.trans hx.symm)
          refine ⟨(box n).source a, hst.1, ?_, ?_⟩
          · rw [← htax]
            exact (data.underlyingGraph_adj_source_target n a).symm
          · rw [← htax]
            exact Sym2.eq_swap
      have hpTail : ∀ g : G.edgeSet, (g : Sym2 V) ∈ p.edges → g ∈ (box n).edges := by
        intro g hg
        apply hp g
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr hg
      obtain ⟨z, hz, q, hq⟩ := ih hpTail y hy
      refine ⟨z, hz, SimpleGraph.Walk.cons hadj q, ?_⟩
      intro b hb
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hb
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
      rcases hb with hb | hb
      · have hba : b.1 = a.1 := by
          apply Subtype.ext
          rw [← data.endpoint n b, ← data.endpoint n a]
          simpa using congrArg (Sym2.map (data.vertex n)) (hb.trans hxy)
        left
        rw [hba]
      · exact Or.inr (hq b hb)

/-- An open underlying-box walk proves the actual labelled connection event.
The premise explicitly excludes the distinguished label at every used edge. -/
lemma reachable_of_underlyingWalk {E : Type*} (B : FK.InfiniteVolume.FiniteBox E)
    (ξ : B.BoundaryPartition) (e : B.edges) (ω : B.Interior) {x y : B.Vertex}
    (q : (underlyingGraph B).Walk x y) :
    (∀ a : B.edges, s(B.source a, B.target a) ∈ q.edges → a ≠ e ∧ ω a = true) →
      (B.graph.connectionGraph ξ (@withEdge _ (fun a b => Classical.propDecidable (a = b)) e false ω)).Reachable x y := by
  induction q with
  | nil => exact fun _ => SimpleGraph.Reachable.refl _
  | @cons x y z hxy q ih =>
      intro hopen
      have htail : ∀ a : B.edges, s(B.source a, B.target a) ∈ q.edges →
          a ≠ e ∧ ω a = true := by
        intro a ha
        apply hopen a
        rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr ha
      apply SimpleGraph.Reachable.trans ?_ (ih htail)
      rcases hxy.2 with hfree | ⟨a, _, hjoin⟩
      · exact (hxy.1 hfree).elim
      · have hpair : s(B.source a, B.target a) = s(x, y) := by
          rcases hjoin with hjoin | hjoin
          · rw [← hjoin.1, ← hjoin.2]
          · rw [← hjoin.1, ← hjoin.2, Sym2.eq_swap]
        have ha : a ≠ e ∧ ω a = true := by
          apply hopen a
          rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inl hpair
        have ha' : @withEdge _ (fun a b => Classical.propDecidable (a = b))
            e false ω a = true := by
          simp [withEdge, ha.1, ha.2]
        exact (show (B.graph.connectionGraph ξ (@withEdge _ (fun a b => Classical.propDecidable (a = b)) e false ω)).Adj x y from
          ⟨hxy.1, Or.inr ⟨a, ha', hjoin⟩⟩).reachable

end FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData

namespace FK.EnhancedTransport

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData
open FK.QuasiTransitive
open FKEnhancement
open FK.Finite.Conditional
open FK.FiniteFiber

/-- The singleton path collection consisting of the selected device's localized
support with its pivot removed. -/
def cyclePathFamily {E : Type*} (B : FiniteBox E) [DecidableEq B.edges]
    (D : E → Finset E) (e : B.edges) : Set (Finset B.edges) :=
  {(activeWithinFinset B (D e.1)).erase e}

/-- Localization into a finite labelled box is injective on global labels. -/
lemma card_activeWithinFinset_le {E : Type*} (B : FiniteBox E) (A : Finset E) :
    (activeWithinFinset B A).card ≤ A.card := by
  classical
  let incl : B.edges ↪ E := Function.Embedding.subtype _
  let mapped := (activeWithinFinset B A).map incl
  have hsub : mapped ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact mem_activeWithinFinset.mp hb
  have hcard := Finset.card_le_card hsub
  simpa only [mapped, Finset.card_map] using hcard

end FK.EnhancedTransport

namespace FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData

open FK.EnhancedTransport
open FK.QuasiTransitive
open FKEnhancement
open FK.Finite.Conditional
open FK.FiniteFiber

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FiniteBox G.edgeSet}

/-- Opening the localized complementary cycle support proves the actual
finite-box connection event, for any boundary partition. -/
lemma graphConnectionEvent_of_cyclePathOpen
    (data : FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData G box)
    (n : ℕ) (hinj : Function.Injective (data.vertex n))
    [DecidableEq (box n).edges] (ξ : (box n).BoundaryPartition) (e : (box n).edges) (D : Finset G.edgeSet)
    (hDsub : D ⊆ (box n).edges) {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (hDcycle : D = walkDevice c) (he : (e.1 : Sym2 V) ∈ c.edges)
    {ω : OpenPath.Config (box n).edges}
    (hopen : OpenPath.OpenEdges ((activeWithinFinset (box n) D).erase e) ω) :
    graphConnectionEvent (box n).graph ξ e (OpenPath.configToBool ω) := by
  classical
  have hevw : (e.1 : Sym2 V) =
      s(data.vertex n ((box n).source e), data.vertex n ((box n).target e)) :=
    (data.endpoint n e).symm
  obtain ⟨p, hp⟩ := exists_alternateWalk_of_mem_cycle c hc he hevw
  have hpBox : ∀ f : G.edgeSet, (f : Sym2 V) ∈ p.edges → f ∈ (box n).edges := by
    intro f hf
    apply hDsub
    rw [hDcycle]
    exact mem_walkDevice.mpr (hp f hf).1
  obtain ⟨y, hy, q, hq⟩ := data.exists_underlyingWalk n hinj p hpBox
    ((box n).source e) rfl
  have hye : y = (box n).target e := hinj hy
  subst y
  unfold graphConnectionEvent endpointsConnectedWithout
  apply reachable_of_underlyingWalk (box n) ξ e (OpenPath.configToBool ω) q
  intro a ha
  have hap : (a.1 : Sym2 V) ∈ p.edges := hq a ha
  have ha' := hp a.1 hap
  have hae : a ≠ e := by
    intro h
    exact ha'.2 (Subtype.ext_iff.mp h)
  have haD : a.1 ∈ D := by
    rw [hDcycle]
    exact mem_walkDevice.mpr ha'.1
  have haAux : a ∈ (activeWithinFinset (box n) D).erase e := by
    exact Finset.mem_erase.mpr ⟨hae, mem_activeWithinFinset.mpr haD⟩
  refine ⟨hae, ?_⟩
  simp [OpenPath.configToBool, OpenPath.bitToBool, hopen a haAux]

end FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData

namespace FK.EnhancedTransport

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.QuasiTransitive
open FKEnhancement

/-- Separation of global devices is exactly the auxiliary-edge condition for
the localized cycle path family. -/
lemma cyclePathFamily_auxiliaryPaths {E : Type*} (B : FiniteBox E)
    [DecidableEq B.edges] (A : Finset E) (S : Set E) (D : E → Finset E)
    (hsep : FKLimit.IsSeparatedDeviceFamily S D) (hAS : ∀ a ∈ A, a ∈ S)
    {e : B.edges} (heS : e.1 ∈ S) :
    OpenPath.AuxiliaryPaths (activeWithinFinset B A) e (cyclePathFamily B D e) := by
  classical
  intro γ hγ
  have hγeq : γ = (activeWithinFinset B (D e.1)).erase e := by
    simpa only [cyclePathFamily, Set.mem_singleton_iff] using hγ
  subst γ
  constructor
  · simp
  · intro f hf hfA
    have hfD : f.1 ∈ D e.1 :=
      mem_activeWithinFinset.mp (Finset.mem_of_mem_erase hf)
    have hfe : f ≠ e := Finset.ne_of_mem_erase hf
    have hfe' : f.1 ≠ e.1 := by
      intro h
      exact hfe (Subtype.ext h)
    exact (hsep e.1 heS).2 f.1 hfD hfe' (hAS f.1 (mem_activeWithinFinset.mp hfA))

/-- A selected global device gives one member of the singleton cycle path
family, and its cardinality inherits the uniform predecessor bound. -/
lemma exists_cyclePathFamily_card_le {E : Type*} (B : FiniteBox E)
    [DecidableEq B.edges] (D : E → Finset E) (e : B.edges) (L : ℕ) (heD : e.1 ∈ D e.1)
    (hcard : (D e.1).card ≤ L) :
    ∃ γ ∈ cyclePathFamily B D e, γ.card ≤ L - 1 := by
  classical
  refine ⟨(activeWithinFinset B (D e.1)).erase e, by simp only [cyclePathFamily,
    Set.mem_singleton_iff], ?_⟩
  have heLocal : e ∈ activeWithinFinset B (D e.1) := mem_activeWithinFinset.mpr heD
  rw [Finset.card_erase_of_mem heLocal]
  exact Nat.sub_le_sub_right ((card_activeWithinFinset_le B (D e.1)).trans hcard) 1

/-- Exact active-cycle certificate for the finite-box premises of
Proposition 4.2.  It simultaneously supplies `AuxiliaryPaths`, the genuine
labelled connection implication, and an auxiliary path of size at most `L-1`.
No locally constant specification or special boundary convention is assumed. -/
theorem cyclePathFamily_spec_of_active
    {V : Type*} {G : SimpleGraph V} {exh : BoxExhaustion G.edgeSet}
    (data : FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : BoundaryAssignment exh.box) (hinj : ∀ n, Function.Injective (data.vertex n))
    {S : Set G.edgeSet} {D : G.edgeSet → Finset G.edgeSet}
    {admissible : ℕ → G.edgeSet → Prop} {L : ℕ}
    (hsep : FKLimit.IsSeparatedDeviceFamily S D)
    (hcycle : ∀ f ∈ S, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      D f = walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcard : ∀ f ∈ S, (D f).card ≤ L)
    {n : ℕ} [DecidableEq (exh.box n).edges] (η : (exh.box n).Exterior)
    (e : (exh.box n).edges)
    (he : e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D admissible n) :
    OpenPath.AuxiliaryPaths (activeWithinFinset (exh.box n)
        (FKLimit.activeEdges (edgeExhaustionOfBox exh) S D admissible n))
        e (cyclePathFamily (exh.box n) D e) ∧
      (∀ {ω : OpenPath.Config (exh.box n).edges},
        OpenPath.SomePathOpen (cyclePathFamily (exh.box n) D e) ω →
          graphConnectionEvent (exh.box n).graph (Φ.partition n η) e
            (OpenPath.configToBool ω)) ∧
      ∃ γ ∈ cyclePathFamily (exh.box n) D e, γ.card ≤ L - 1 := by
  classical
  have he' := FKLimit.mem_activeEdges.mp he
  refine ⟨cyclePathFamily_auxiliaryPaths (exh.box n)
      (FKLimit.activeEdges (edgeExhaustionOfBox exh) S D admissible n) S D hsep
      (fun a ha => FKLimit.activeEdges_subset ha) he'.2.1, ?_, ?_⟩
  · obtain ⟨v, c, hc, _, hDcycle, heC⟩ := hcycle e.1 he'.2.1
    intro ω hω
    obtain ⟨γ, hγ, hopen⟩ := hω
    have hγeq : γ = (activeWithinFinset (exh.box n) (D e.1)).erase e := by
      simpa only [cyclePathFamily, Set.mem_singleton_iff] using hγ
    subst γ
    exact data.graphConnectionEvent_of_cyclePathOpen n (hinj n) (Φ.partition n η)
      e (D e.1) he'.2.2.1 c hc hDcycle heC hopen
  · exact exists_cyclePathFamily_card_le (exh.box n) D e L
      (hsep e.1 he'.2.1).1 (hcard e.1 he'.2.1)

end FK.EnhancedTransport

#print axioms FK.QuasiTransitive.exists_alternateWalk_of_mem_cycle
#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.exists_underlyingWalk
#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.reachable_of_underlyingWalk
#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.graphConnectionEvent_of_cyclePathOpen
#print axioms FK.EnhancedTransport.card_activeWithinFinset_le
#print axioms FK.EnhancedTransport.cyclePathFamily_auxiliaryPaths
#print axioms FK.EnhancedTransport.exists_cyclePathFamily_card_le
#print axioms FK.EnhancedTransport.cyclePathFamily_spec_of_active

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology
open FKEnhancement

noncomputable section

/-- Direct integration of the finite-box cycle certificate into the existing
upper active-cycle DLR comparison.  The only geometric condition needed to lift
walks is injectivity of the compatible box vertex map. -/
theorem lt_dlr_upper_of_active_cyclePathFamily
    {V : Type*} {G : SimpleGraph V} [Countable G.edgeSet]
    (exh : FK.InfiniteVolume.BoxExhaustion G.edgeSet)
    (data : FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData G exh.box)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (hp : (p : ℝ) ∈ Ioo 0 1) (hqR : 0 < (q : ℝ))
    (hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ))
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet)
    (cycleAdmissible : ℕ → G.edgeSet → Prop) (L : ℕ)
    (hsep : FKLimit.IsSeparatedDeviceFamily S D)
    (hcycleAdm : ∀ e ∈ S, ∀ᶠ n in atTop, cycleAdmissible n e)
    (hcycle : ∀ f ∈ S, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
      D f = FK.QuasiTransitive.walkDevice c ∧ (f : Sym2 V) ∈ c.edges)
    (hcard : ∀ f ∈ S, (D f).card ≤ L)
    (hne : ∀ n, Nonempty (exh.box n).edges) :
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct
        (FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L S)) μ := by
  let Γ : ∀ n (_ : (exh.box n).Exterior),
      (exh.box n).edges → Set (Finset (exh.box n).edges) :=
    fun n _ e => cyclePathFamily (exh.box n) D e
  apply lt_dlr_upper_of_active_cycle_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
    S D cycleAdmissible L hsep hcycleAdm hne Γ
  · intro n η e he
    have he' : e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D
        cycleAdmissible n := mem_activeWithinFinset.mp he
    exact (cyclePathFamily_spec_of_active data Φ hinj hsep hcycle hcard η e he').1
  · intro n η e he ω hω
    have he' : e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh) S D
        cycleAdmissible n := mem_activeWithinFinset.mp he
    exact (cyclePathFamily_spec_of_active data Φ hinj hsep hcycle hcard η e he').2.1 hω
  · intro n η e he
    exact (cyclePathFamily_spec_of_active data Φ hinj hsep hcycle hcard η e he).2.2

end
end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.lt_dlr_upper_of_active_cyclePathFamily
