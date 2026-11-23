import FK.AGDeviceEssentiality

/-!
# Genuine simultaneous annular sleeves

For a simple graph `H`, `sleeveGraph H` retains every original bond and adds,
for each original bond, a new middle vertex and a two-edge path between the
bond's endpoints.  One shared activation opens the two-edge bypasses of any
finite collection of original bonds.  Consequently closing that whole
collection can be repaired simultaneously by actual replacement walks.

This is a concrete simple-graph construction, not the unsupported assertion
that every essential enhancement on every quasi-transitive graph has annular
rerouting.  No strict critical-point shift is claimed here.
-/

open Set
open scoped BigOperators Sym2

namespace FK.AGImplant

open FK.EssentialEnhancement FK.AGPeeling
open CurvatureVariance.Infra.Percolation

universe u v

namespace Sleeve

variable {V : Type u} (H : SimpleGraph V)

/-- Add one distinct two-edge bypass to every bond of `H`, while retaining the
bond itself.  The graph is simple by construction. -/
def graph : SimpleGraph (V ⊕ H.edgeSet) where
  Adj
    | Sum.inl x, Sum.inl y => H.Adj x y
    | Sum.inl x, Sum.inr e => x ∈ (e : Sym2 V)
    | Sum.inr e, Sum.inl x => x ∈ (e : Sym2 V)
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact hxy.symm
        | inr e => exact hxy
    | inr e =>
        cases y with
        | inl y => exact hxy
        | inr f => exact hxy.elim⟩
  loopless := ⟨by
    intro x
    cases x with
    | inl x => exact H.loopless.irrefl x
    | inr e => exact id⟩

/-- An original bond, embedded in the sleeved graph with the canonical
endpoints supplied by `Sym2.out`. -/
noncomputable def baseEdge (e : H.edgeSet) : (graph H).edgeSet :=
  ⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2), by
    change H.Adj (e : Sym2 V).out.1 (e : Sym2 V).out.2
    have he : s((e : Sym2 V).out.1, (e : Sym2 V).out.2) = (e : Sym2 V) :=
      Quot.out_eq _
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.property⟩

/-- The first edge of the explicit two-edge bypass of `e`. -/
noncomputable def leftSpoke (e : H.edgeSet) : (graph H).edgeSet :=
  ⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inr e), Sym2.out_fst_mem (e : Sym2 V)⟩

/-- The second edge of the explicit two-edge bypass of `e`. -/
noncomputable def rightSpoke (e : H.edgeSet) : (graph H).edgeSet :=
  ⟨s(Sum.inr e, Sum.inl (e : Sym2 V).out.2), Sym2.out_snd_mem (e : Sym2 V)⟩

lemma baseEdge_ne_leftSpoke (e f : H.edgeSet) :
    baseEdge H e ≠ leftSpoke H f := by
  intro h
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2) =
    s(Sum.inl (f : Sym2 V).out.1, Sum.inr f) at hval
  rcases Sym2.eq_iff.mp hval with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp at h₂
  · simp at h₁

lemma baseEdge_ne_rightSpoke (e f : H.edgeSet) :
    baseEdge H e ≠ rightSpoke H f := by
  intro h
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2) =
    s(Sum.inr f, Sum.inl (f : Sym2 V).out.2) at hval
  rcases Sym2.eq_iff.mp hval with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp at h₁
  · simp at h₂

/-- The bypass contains all the edges activated for a finite collection of
original bonds. -/
noncomputable def edges (S : Finset H.edgeSet) : Finset (graph H).edgeSet := by
  classical
  exact S.biUnion fun e => {leftSpoke H e, rightSpoke H e}

/-- A single shared-activation device opening all selected bypasses. -/
noncomputable def support (S : Finset H.edgeSet) : Unit → Set (graph H).edgeSet :=
  fun _ => ↑(edges H S)

/-- The finite annulus consisting of the selected original bonds. -/
noncomputable def annulus (S : Finset H.edgeSet) : Finset (graph H).edgeSet := by
  classical
  exact S.image (baseEdge H)

@[simp] lemma baseEdge_mem_annulus (S : Finset H.edgeSet) {e : H.edgeSet}
    (he : e ∈ S) : baseEdge H e ∈ annulus H S := by
  classical
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

@[simp] lemma leftSpoke_mem_edges (S : Finset H.edgeSet) {e : H.edgeSet}
    (he : e ∈ S) : leftSpoke H e ∈ edges H S := by
  classical
  apply Finset.mem_biUnion.mpr
  exact ⟨e, he, by simp⟩

@[simp] lemma rightSpoke_mem_edges (S : Finset H.edgeSet) {e : H.edgeSet}
    (he : e ∈ S) : rightSpoke H e ∈ edges H S := by
  classical
  apply Finset.mem_biUnion.mpr
  exact ⟨e, he, by simp⟩

/-- One activation uses at most two edges per selected original bond. -/
lemma card_edges_le (S : Finset H.edgeSet) : (edges H S).card ≤ 2 * S.card := by
  classical
  calc
    (edges H S).card ≤ ∑ e ∈ S, ({leftSpoke H e, rightSpoke H e} :
        Finset (graph H).edgeSet).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ S, 2 := by
      apply Finset.sum_le_sum
      intro e he
      simpa using (Finset.card_insert_le (a := leftSpoke H e)
        (s := {rightSpoke H e}))
    _ = 2 * S.card := by simp [mul_comm]

/-- No original annular bond is itself in the activation support: the new
theorem really uses its bypasses, not the old support-contained criterion. -/
lemma baseEdge_not_mem_edges (S : Finset H.edgeSet) (e : H.edgeSet) :
    baseEdge H e ∉ edges H S := by
  classical
  intro h
  have h' : ∃ f ∈ S, baseEdge H e ∈
      ({leftSpoke H f, rightSpoke H f} : Finset (graph H).edgeSet) := by
    apply Finset.mem_biUnion.mp
    simpa only [edges] using h
  obtain ⟨f, hf, hmem⟩ := h'
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem.elim (baseEdge_ne_leftSpoke H e f) (baseEdge_ne_rightSpoke H e f)

/-- After activation, both spokes of every selected bypass are genuinely open,
independently of all ordinary bond coordinates. -/
lemma open_bypass (S : Finset H.edgeSet) {e : H.edgeSet} (he : e ∈ S)
    (χ : JointConfig (graph H).edgeSet Unit) :
    OpenConnected (graph H)
      (deviceConfig (support H S)
        (forceEdge (annularClose (annulus H S) χ) (Sum.inr ()) true))
      Set.univ (Sum.inl (e : Sym2 V).out.1) (Sum.inl (e : Sym2 V).out.2) := by
  have hleft : deviceConfig (support H S)
      (forceEdge (annularClose (annulus H S) χ) (Sum.inr ()) true)
      (leftSpoke H e) = true := by
    apply deviceConfig_eq_true_of_mem (support H S) _ ()
    · exact forceEdge_same _ _ _
    · exact_mod_cast leftSpoke_mem_edges H S he
  have hright : deviceConfig (support H S)
      (forceEdge (annularClose (annulus H S) χ) (Sum.inr ()) true)
      (rightSpoke H e) = true := by
    apply deviceConfig_eq_true_of_mem (support H S) _ ()
    · exact forceEdge_same _ _ _
    · exact_mod_cast rightSpoke_mem_edges H S he
  have hleftAdj : (graph H).Adj
      (Sum.inl (e : Sym2 V).out.1) (Sum.inr e) := Sym2.out_fst_mem (e : Sym2 V)
  have hrightAdj : (graph H).Adj
      (Sum.inr e) (Sum.inl (e : Sym2 V).out.2) := Sym2.out_snd_mem (e : Sym2 V)
  apply (OpenConnected.of_adj hleftAdj (Set.mem_univ _) ?_).trans
  · apply OpenConnected.of_adj hrightAdj (Set.mem_univ _)
    change deviceConfig (support H S) _ (rightSpoke H e) = true
    exact hright
  · change deviceConfig (support H S) _ (leftSpoke H e) = true
    exact hleft

lemma baseEdge_adj (e : H.edgeSet) :
    (graph H).Adj (Sum.inl (e : Sym2 V).out.1)
      (Sum.inl (e : Sym2 V).out.2) :=
  (baseEdge H e).property

lemma baseEdge_eq (e : H.edgeSet)
    (h : (graph H).Adj (Sum.inl (e : Sym2 V).out.1)
      (Sum.inl (e : Sym2 V).out.2)) :
    (⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2), h⟩ :
      (graph H).edgeSet) = baseEdge H e := by
  apply Subtype.ext
  rfl

lemma baseEdge_val (e : H.edgeSet) :
    (baseEdge H e : Sym2 (V ⊕ H.edgeSet)) = Sym2.map Sum.inl (e : Sym2 V) := by
  calc
    (baseEdge H e : Sym2 (V ⊕ H.edgeSet)) =
        Sym2.map Sum.inl s((e : Sym2 V).out.1, (e : Sym2 V).out.2) := rfl
    _ = Sym2.map Sum.inl (e : Sym2 V) := congrArg (Sym2.map Sum.inl) (Quot.out_eq _)

lemma baseEdge_injective : Function.Injective (baseEdge H) := by
  intro e f hef
  apply Subtype.ext
  have hval := congrArg Subtype.val hef
  rw [baseEdge_val, baseEdge_val] at hval
  exact (Sym2.map.injective Sum.inl_injective) hval

@[simp] lemma card_annulus (S : Finset H.edgeSet) :
    (annulus H S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S (baseEdge_injective H)

lemma mem_annulus {S : Finset H.edgeSet} {f : (graph H).edgeSet} :
    f ∈ annulus H S ↔ ∃ e ∈ S, baseEdge H e = f := by
  classical
  exact Finset.mem_image

/-- The annulus and its activated sleeve are disjoint, so this is genuinely
not the previously proved support-contained criterion. -/
lemma disjoint_annulus_edges (S : Finset H.edgeSet) :
    Disjoint (annulus H S) (edges H S) := by
  classical
  rw [Finset.disjoint_left]
  intro f hfan hfedges
  obtain ⟨e, he, rfl⟩ := (mem_annulus H (S := S) (f := f)).mp hfan
  exact baseEdge_not_mem_edges H S e hfedges

/-- Every edge in the selected annulus, not only an edge contained in the
activation support, has an actual two-edge replacement walk after activation.
The two orientations of a simple-graph edge are both handled explicitly. -/
lemma annular_replacement (S : Finset H.edgeSet)
    {χ : JointConfig (graph H).edgeSet Unit} {x y : V ⊕ H.edgeSet}
    (hxy : (graph H).Adj x y)
    (hf : (⟨s(x, y), hxy⟩ : (graph H).edgeSet) ∈ annulus H S) :
    OpenConnected (graph H)
      (deviceConfig (support H S)
        (forceEdge (annularClose (annulus H S) χ) (Sum.inr ()) true))
      Set.univ x y := by
  obtain ⟨e, he, hef⟩ := mem_annulus H (S := S) (f := ⟨s(x, y), hxy⟩) |>.mp hf
  have hval := congrArg Subtype.val hef
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2) = s(x, y) at hval
  rcases Sym2.eq_iff.mp hval with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · cases hx
    cases hy
    exact open_bypass H S he χ
  · cases hx
    cases hy
    exact openConnected_reverse (open_bypass H S he χ)

/-- Simultaneous annular replacement converts a pivot of any selected original
bond into a pivot of the shared sleeve activation.  The statement is valid on
infinite as well as finite sleeved graphs: no finite-edge instance is used. -/
theorem activationPivotal_openConnected_annulus (S : Finset H.edgeSet)
    {e : H.edgeSet} (he : e ∈ S) {a b : V ⊕ H.edgeSet}
    {χ : JointConfig (graph H).edgeSet Unit}
    (hpiv : EdgePivotal
      (deviceEvent (support H S) {ω | OpenConnected (graph H) ω Set.univ a b})
      (baseEdge H e) χ) :
    ActivationPivotal
      (deviceEvent (support H S) {ω | OpenConnected (graph H) ω Set.univ a b}) ()
      (annularClose (annulus H S) χ) := by
  classical
  rw [← baseEdge_eq H e (baseEdge_adj H e)] at hpiv
  apply activationPivotal_openConnected_annularClose (baseEdge_adj H e)
    (annulus H S) (by
      have hm := baseEdge_mem_annulus H S he
      rwa [← baseEdge_eq H e (baseEdge_adj H e)] at hm) (support H S) ()
  intro ξ x y hxy hf
  exact annular_replacement H S y hf
  exact hpiv

/-- The same simultaneous construction for the repository's actual one-arm
event, including the infinite-graph geometric case. -/
theorem activationPivotal_deviceArmEvent_annulus (S : Finset H.edgeSet)
    {e : H.edgeSet} (he : e ∈ S) {o : V ⊕ H.edgeSet} (n : ℕ)
    {χ : JointConfig (graph H).edgeSet Unit}
    (hpiv : EdgePivotal (deviceArmEvent (graph H) (support H S) o n)
      (baseEdge H e) χ) :
    ActivationPivotal (deviceArmEvent (graph H) (support H S) o n) ()
      (annularClose (annulus H S) χ) := by
  classical
  rw [← baseEdge_eq H e (baseEdge_adj H e)] at hpiv
  apply activationPivotal_deviceArmEvent_annularClose (baseEdge_adj H e)
    (annulus H S) (by
      have hm := baseEdge_mem_annulus H S he
      rwa [← baseEdge_eq H e (baseEdge_adj H e)] at hm) (support H S) () n
  intro ξ x y hxy hf
  exact annular_replacement H S y hf
  exact hpiv

/-- Only the finitely many incident base edges are needed at an original
vertex. -/
lemma finite_edges_containing [H.LocallyFinite] (x : V) :
    Finite {e : H.edgeSet // x ∈ (e : Sym2 V)} := by
  classical
  let f : {e : H.edgeSet // x ∈ (e : Sym2 V)} → H.incidenceSet x :=
    fun e => ⟨(e.1 : Sym2 V), e.1.property, e.2⟩
  have hf : Function.Injective f := by
    intro e g heg
    apply Subtype.ext
    apply Subtype.ext
    change (e.1 : Sym2 V) = (g.1 : Sym2 V)
    exact congrArg (fun w : H.incidenceSet x => (w : Sym2 V)) heg
  exact Finite.of_injective f hf

/-- Sleeving preserves local finiteness.  At an original vertex the neighbours
inject into base neighbours plus incident base edges; at a midpoint there are
only the two endpoint neighbours. -/
noncomputable instance graphLocallyFinite [H.LocallyFinite] : (graph H).LocallyFinite := by
  classical
  intro v
  cases v with
  | inl x =>
      let f : (graph H).neighborSet (Sum.inl x) →
          H.neighborSet x ⊕ {e : H.edgeSet // x ∈ (e : Sym2 V)} := fun w =>
        match w with
        | ⟨Sum.inl y, hy⟩ => Sum.inl ⟨y, hy⟩
        | ⟨Sum.inr e, he⟩ => Sum.inr ⟨e, he⟩
      have hf : Function.Injective f := by
        rintro ⟨y₁ | e₁, h₁⟩ ⟨y₂ | e₂, h₂⟩ h
        · simp [f] at h ⊢
          exact congrArg Subtype.val h
        · simp [f] at h
        · simp [f] at h
        · simp [f] at h ⊢
          exact congrArg Subtype.val h
      letI : Finite {e : H.edgeSet // x ∈ (e : Sym2 V)} :=
        finite_edges_containing H x
      letI : Finite ((graph H).neighborSet (Sum.inl x)) :=
        Finite.of_injective f hf
      exact Fintype.ofFinite _
  | inr e =>
      have hsub : (graph H).neighborSet (Sum.inr e) ⊆
          ({Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2} :
            Set (V ⊕ H.edgeSet)) := by
        intro w hw
        cases w with
        | inl x =>
            change x ∈ (e : Sym2 V) at hw
            rw [← Quot.out_eq (e : Sym2 V), Sym2.mem_iff] at hw
            rcases hw with rfl | rfl <;> simp
        | inr f => exact hw.elim
      exact (((Set.finite_singleton _).insert _).subset hsub).fintype

/-- The inclusion of original vertices is a genuine graph homomorphism. -/
def baseHom : H →g graph H where
  toFun := Sum.inl
  map_rel' := fun h => h

/-- Every added midpoint is adjacent to its first canonical endpoint. -/
lemma midpoint_reachable (e : H.edgeSet) :
    (graph H).Reachable (Sum.inr e) (Sum.inl (e : Sym2 V).out.1) := by
  have h : (graph H).Adj (Sum.inl (e : Sym2 V).out.1) (Sum.inr e) :=
    Sym2.out_fst_mem (e : Sym2 V)
  exact h.symm.reachable

/-- Sleeving preserves connectedness; new midpoints are not left as extra
components. -/
lemma graphConnected (hconn : H.Connected) : (graph H).Connected where
  nonempty := hconn.nonempty.map Sum.inl
  preconnected := by
    intro x y
    cases x with
    | inl x =>
        cases y with
        | inl y => exact (hconn x y).map (baseHom H)
        | inr e =>
            exact ((hconn x (e : Sym2 V).out.1).map (baseHom H)).trans
              (midpoint_reachable H e).symm
    | inr e =>
        cases y with
        | inl y =>
            exact (midpoint_reachable H e).trans
              ((hconn ((e : Sym2 V).out.1) y).map (baseHom H))
        | inr f =>
            exact (midpoint_reachable H e).trans
              (((hconn ((e : Sym2 V).out.1) ((f : Sym2 V).out.1)).map
                (baseHom H)).trans (midpoint_reachable H f).symm)

/-- A base automorphism lifts to the sleeved graph, sending each bypass
midpoint to the midpoint of the mapped base edge. -/
def automorphism (φ : H ≃g H) : graph H ≃g graph H where
  toEquiv := Equiv.sumCongr φ.toEquiv φ.mapEdgeSet
  map_rel_iff' := by
    intro x y
    cases x with
    | inl x =>
        cases y with
        | inl y => exact φ.map_adj_iff
        | inr e =>
            change φ x ∈ Sym2.map φ (e : Sym2 V) ↔ x ∈ (e : Sym2 V)
            rw [Sym2.mem_map]
            constructor
            · rintro ⟨a, ha, hax⟩
              have : a = x := φ.injective hax
              simpa [this] using ha
            · intro hx
              exact ⟨x, hx, rfl⟩
    | inr e =>
        cases y with
        | inl y =>
            change φ y ∈ Sym2.map φ (e : Sym2 V) ↔ y ∈ (e : Sym2 V)
            rw [Sym2.mem_map]
            constructor
            · rintro ⟨a, ha, hay⟩
              have : a = y := φ.injective hay
              simpa [this] using ha
            · intro hy
              exact ⟨y, hy, rfl⟩
        | inr f => exact Iff.rfl

lemma orbit_eq_of_automorphism {x y : V ⊕ H.edgeSet}
    (ψ : graph H ≃g graph H) (h : ψ x = y) :
    (Quotient.mk'' x : MulAction.orbitRel.Quotient (graph H ≃g graph H)
      (V ⊕ H.edgeSet)) = Quotient.mk'' y := by
  apply Quotient.sound
  change MulAction.orbitRel (graph H ≃g graph H) (V ⊕ H.edgeSet) x y
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨ψ.symm, ?_⟩
  rw [← h]
  exact ψ.symm_apply_apply x

/-- Under vertex- and edge-transitivity of `H`, the sleeved graph has exactly
the original-vertex and midpoint orbit classes, hence is quasi-transitive.
The two transitivity hypotheses are deliberately explicit; no general finite
edge-orbit theorem is being smuggled in. -/
lemma graphQuasiTransitive_of_vertex_edge_transitive
    [Nonempty V] [Nonempty H.edgeSet]
    (hvertex : ∀ x y : V, ∃ φ : H ≃g H, φ x = y)
    (hedge : ∀ e f : H.edgeSet, ∃ φ : H ≃g H, φ.mapEdgeSet e = f) :
    FK.QuasiTransitive.IsQuasiTransitive (graph H) := by
  let v₀ : V := Classical.choice (inferInstance : Nonempty V)
  let e₀ : H.edgeSet := Classical.choice (inferInstance : Nonempty H.edgeSet)
  let rep : Bool → V ⊕ H.edgeSet := fun b =>
    if b then Sum.inr e₀ else Sum.inl v₀
  have hsurj : Function.Surjective (fun b =>
      (Quotient.mk'' (rep b) : MulAction.orbitRel.Quotient (graph H ≃g graph H)
        (V ⊕ H.edgeSet))) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro v
    cases v with
    | inl x =>
        obtain ⟨φ, hφ⟩ := hvertex v₀ x
        refine ⟨false, ?_⟩
        change (Quotient.mk'' (Sum.inl v₀) :
          MulAction.orbitRel.Quotient (graph H ≃g graph H) (V ⊕ H.edgeSet)) =
            Quotient.mk'' (Sum.inl x)
        apply orbit_eq_of_automorphism H (automorphism H φ)
        exact congrArg Sum.inl hφ
    | inr e =>
        obtain ⟨φ, hφ⟩ := hedge e₀ e
        refine ⟨true, ?_⟩
        change (Quotient.mk'' (Sum.inr e₀) :
          MulAction.orbitRel.Quotient (graph H ≃g graph H) (V ⊕ H.edgeSet)) =
            Quotient.mk'' (Sum.inr e)
        apply orbit_eq_of_automorphism H (automorphism H φ)
        exact congrArg Sum.inr hφ
  exact Finite.of_surjective _ hsurj

/-- Exact finite-product consequence of the simultaneous sleeves.  The
ordinary independent bond law and activation law retain the exact likelihood
ratio and fibre constants of the general annular transport. -/
theorem openConnected_annulus_edgePivotal_event_mul_le
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (bond : (graph H).edgeSet → OpenPath.FinProb Bool)
    (activation : Unit → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (S : Finset H.edgeSet) {e : H.edgeSet} (he : e ∈ S)
    {a b : V ⊕ H.edgeSet} :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ S.card * μ.event {χ | EdgePivotal
        (deviceEvent (support H S)
          {ω | OpenConnected (graph H) ω Set.univ a b}) (baseEdge H e) χ} ≤
      ((2 ^ S.card : ℕ) : ℝ) * μ.event {χ | ActivationPivotal
        (deviceEvent (support H S)
          {ω | OpenConnected (graph H) ω Set.univ a b}) () χ} := by
  classical
  dsimp only
  have hm : (⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2),
      baseEdge_adj H e⟩ : (graph H).edgeSet) ∈ annulus H S := by
    rw [baseEdge_eq H e (baseEdge_adj H e)]
    exact baseEdge_mem_annulus H S he
  have h := openConnected_annular_edgePivotal_event_mul_le (a := a) (b := b)
    bond activation δ hδ hbond hactivation (baseEdge_adj H e) (annulus H S) hm (support H S) () (by
      intro ξ x y hxy hopen hf
      exact annular_replacement H S hxy hf)
  rw [baseEdge_eq H e (baseEdge_adj H e)] at h
  simpa only [card_annulus] using h

/-- The exact finite-product comparison for the actual one-arm event, with no
support-containment assumption on the annulus. -/
theorem deviceArmEvent_annulus_edgePivotal_event_mul_le
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (bond : (graph H).edgeSet → OpenPath.FinProb Bool)
    (activation : Unit → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (S : Finset H.edgeSet) {e : H.edgeSet} (he : e ∈ S)
    {o : V ⊕ H.edgeSet} (n : ℕ) :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ S.card * μ.event {χ | EdgePivotal
        (deviceArmEvent (graph H) (support H S) o n) (baseEdge H e) χ} ≤
      ((2 ^ S.card : ℕ) : ℝ) * μ.event {χ | ActivationPivotal
        (deviceArmEvent (graph H) (support H S) o n) () χ} := by
  classical
  dsimp only
  have hm : (⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2),
      baseEdge_adj H e⟩ : (graph H).edgeSet) ∈ annulus H S := by
    rw [baseEdge_eq H e (baseEdge_adj H e)]
    exact baseEdge_mem_annulus H S he
  have h := deviceArmEvent_annular_edgePivotal_event_mul_le (o := o)
    bond activation δ hδ hbond hactivation (baseEdge_adj H e) (annulus H S) hm (support H S) () n (by
      intro ξ x y hxy hopen hf
      exact annular_replacement H S hxy hf)
  rw [baseEdge_eq H e (baseEdge_adj H e)] at h
  simpa only [card_annulus] using h

end Sleeve

end FK.AGImplant
