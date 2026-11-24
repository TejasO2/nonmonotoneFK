import FK.OneEdgeNoEscape

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

attribute [local instance] Classical.propDecidable Classical.decPred

universe u v w

namespace FK.InfiniteVolume
namespace NoEscape

/-- The finite set of configurations lying in a given event. -/
noncomputable def cfgFinset (G : FK.Finite.LabelledMultigraph.{0, 0}) (T : Set G.Configuration) :
    Finset G.Configuration := by
  classical
  letI : Fintype G.Configuration := G.instFintypeConfiguration
  exact Finset.univ.filter (fun C : G.Configuration => C ∈ T)

/-- `Finset.univ` does not depend on the chosen `Fintype` instance. -/
lemma univ_congr_fintype {α : Type*} (i₁ i₂ : Fintype α) :
    (@Finset.univ α i₁) = (@Finset.univ α i₂) :=
  congrArg (fun i : Fintype α => @Finset.univ α i) (Subsingleton.elim i₁ i₂)

/-- Dividing a finite sum by a constant. -/
lemma sum_div_eq {α : Type*} (s : Finset α) (f : α → ℝ≥0∞) (a : ℝ≥0∞) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (ENNReal.div_eq_inv_mul).symm

@[simp] lemma coe_cfgFinset (G : FK.Finite.LabelledMultigraph.{0, 0}) (T : Set G.Configuration) :
    ((cfgFinset G T : Finset G.Configuration) : Set G.Configuration) = T := by
  ext a; simp [cfgFinset]

/-- The partition function as a sum of FK weights over all configurations. -/
lemma partitionFunction_coe (G : FK.Finite.LabelledMultigraph.{0, 0}) {q p : NNReal}
    (ξ : G.BoundaryPartition) :
    ((G.partitionFunction q p ξ : NNReal) : ℝ≥0∞)
      = ∑ ω : G.Configuration, ((G.fkWeight q p ξ ω : NNReal) : ℝ≥0∞) := by
  rw [FK.Finite.LabelledMultigraph.partitionFunction]
  push_cast
  rfl

variable {V : Type*} [Fintype V]

/-- An isolated-vertex extension: if every edge of `H` has both endpoints in `t`,
then the number of connected components of `H` is the number of components of the
induced graph on `t` plus the number of vertices outside `t`. -/
theorem card_connectedComponent_induce_add (H : SimpleGraph V) (t : Set V)
    (ht : ∀ u v, H.Adj u v → u ∈ t ∧ v ∈ t) :
    Nat.card H.ConnectedComponent =
      Nat.card (H.induce t).ConnectedComponent + Nat.card {v : V // v ∉ t} := by
  classical
  let f : V → (H.induce t).ConnectedComponent ⊕ {v : V // v ∉ t} := fun v =>
    if h : v ∈ t then Sum.inl ((H.induce t).connectedComponentMk ⟨v, h⟩) else Sum.inr ⟨v, h⟩
  have hf_in : ∀ (v : V) (h : v ∈ t),
      f v = Sum.inl ((H.induce t).connectedComponentMk ⟨v, h⟩) := by
    intro v h; simp only [f]; rw [dif_pos h]
  have hf_out : ∀ (v : V) (h : v ∉ t), f v = Sum.inr ⟨v, h⟩ := by
    intro v h; simp only [f]; rw [dif_neg h]
  have hadj : ∀ u v, H.Adj u v → f u = f v := by
    intro u v huv
    obtain ⟨hu, hv⟩ := ht u v huv
    rw [hf_in u hu, hf_in v hv]
    congr 1
    exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable
      (show (H.induce t).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv))
  have hwalk : ∀ (u v : V) (p : H.Walk u v), f u = f v := by
    intro u v p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  let g : H.ConnectedComponent → (H.induce t).ConnectedComponent ⊕ {v : V // v ∉ t} :=
    SimpleGraph.ConnectedComponent.lift f (fun v w p _ => hwalk v w p)
  have hg : ∀ v, g (H.connectedComponentMk v) = f v := fun v => rfl
  have hsurj : Function.Surjective g := by
    intro z
    rcases z with D | w
    · obtain ⟨v, hv⟩ := D.exists_rep
      refine ⟨H.connectedComponentMk v.1, ?_⟩
      rw [hg, hf_in v.1 v.2]
      exact congrArg Sum.inl hv
    · refine ⟨H.connectedComponentMk w.1, ?_⟩
      rw [hg, hf_out w.1 w.2]
  have hmapind : ∀ (a b : ↑t), (H.induce t).Reachable a b → H.Reachable a.1 b.1 := by
    intro a b h
    exact h.map ⟨Subtype.val, fun {_ _} hadj => hadj⟩
  have hinj : Function.Injective g := by
    intro C C' hCC'
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      induction C' using SimpleGraph.ConnectedComponent.ind with
      | h w =>
        rw [hg, hg] at hCC'
        by_cases hv : v ∈ t
        · by_cases hw : w ∈ t
          · rw [hf_in v hv, hf_in w hw] at hCC'
            have hD : (H.induce t).connectedComponentMk ⟨v, hv⟩ =
                (H.induce t).connectedComponentMk ⟨w, hw⟩ := Sum.inl.inj hCC'
            have hreach : (H.induce t).Reachable ⟨v, hv⟩ ⟨w, hw⟩ :=
              SimpleGraph.ConnectedComponent.exact hD
            exact SimpleGraph.ConnectedComponent.sound (hmapind _ _ hreach)
          · rw [hf_in v hv, hf_out w hw] at hCC'
            exact absurd hCC' (by simp)
        · by_cases hw : w ∈ t
          · rw [hf_out v hv, hf_in w hw] at hCC'
            exact absurd hCC'.symm (by simp)
          · rw [hf_out v hv, hf_out w hw] at hCC'
            have : v = w := congrArg Subtype.val (Sum.inr.inj hCC')
            subst this; rfl
  calc Nat.card H.ConnectedComponent
      = Nat.card ((H.induce t).ConnectedComponent ⊕ {v : V // v ∉ t}) :=
        Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)
    _ = _ + _ := Nat.card_sum

end NoEscape
end FK.InfiniteVolume

namespace FK.InfiniteVolume
namespace NoEscape

open FK.Finite

/-! ## Part 2: monotone events and positive association -/

section Events

variable {E : Type*}

/-- An increasing (upward closed) event on configurations. -/
def IsUp (A : Set (E → Bool)) : Prop := ∀ ω ∈ A, ∀ η, ω ≤ η → η ∈ A

/-- A decreasing (downward closed) event on configurations. -/
def IsDown (A : Set (E → Bool)) : Prop := ∀ ω ∈ A, ∀ η, η ≤ ω → η ∈ A

end Events

/-- **Positive association (FKG) of the finite random-cluster measures at `q ≥ 1`.**
This is the single model-specific input of this module: increasing events are
nonnegatively correlated under every normalized finite FK measure, with an
arbitrary boundary setoid, loops and parallel labels retained. -/
def PosAssoc (q p : NNReal) (hq : 0 < q) (hp : p ≤ 1) : Prop :=
  ∀ (G : LabelledMultigraph.{0, 0}) (ξ : G.BoundaryPartition) (A D : Set (G.Edge → Bool)),
    IsUp A → IsDown D →
      G.fkMeasure hq hp ξ (A ∩ D) ≤ G.fkMeasure hq hp ξ A * G.fkMeasure hq hp ξ D

end NoEscape
end FK.InfiniteVolume

namespace FK.InfiniteVolume
namespace NoEscape

open FK.Finite

/-! ## Part 3: adding edges increases increasing-event probabilities (given FKG) -/

section EdgeGrowth

variable {V : Type*} [Fintype V]
variable {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]

/-- The labelled multigraph on the vertex type `V` with edge type `E` and the
given endpoints. -/
@[reducible] def fgOf (E : Type) [Fintype E] (src tgt : E → V) : LabelledMultigraph where
  Vertex := V
  Edge := E
  source := src
  target := tgt

variable {src₁ : E₁ → V} {tgt₁ : E₁ → V} {src₂ : E₂ → V} {tgt₂ : E₂ → V}
variable {ι : E₁ → E₂}

/-- Restriction of an `E₂`-configuration to the embedded edge type `E₁`. -/
def res (ι : E₁ → E₂) (B : E₂ → Bool) : E₁ → Bool := fun e => B (ι e)

/-- The configurations that are closed on every edge outside the embedded copy. -/
def ClosedOutside (ι : E₁ → E₂) : Set (E₂ → Bool) :=
  {B | ∀ e : E₂, (¬ ∃ a : E₁, ι a = e) → B e = false}

lemma mem_closedOutside {ι : E₁ → E₂} {B : E₂ → Bool} :
    B ∈ ClosedOutside ι ↔ ∀ e : E₂, (¬ ∃ a : E₁, ι a = e) → B e = false := Iff.rfl

/-- Every edge of `E₂` outside the embedded copy has closed value, so the number
of components only depends on the restricted configuration. -/
theorem connectionGraph_res {ξ : Setoid V} {B : E₂ → Bool} (hB : B ∈ ClosedOutside ι)
    (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e) :
    (fgOf E₂ src₂ tgt₂).connectionGraph ξ B
      = (fgOf E₁ src₁ tgt₁).connectionGraph ξ (res ι B) := by
  classical
  simp only [ClosedOutside] at hB
  ext u v
  simp only [fgOf, LabelledMultigraph.connectionGraph, LabelledMultigraph.Joins, res]
  constructor
  · rintro ⟨huv, hw | ⟨e, he, hjoin⟩⟩
    · exact ⟨huv, Or.inl hw⟩
    · have hne : ¬ (¬ ∃ a : E₁, ι a = e) := fun h => by rw [hB e h] at he; exact Bool.noConfusion he
      obtain ⟨a, ha⟩ := not_not.mp hne
      subst ha
      refine ⟨huv, Or.inr ⟨a, he, ?_⟩⟩
      rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [← hsrc a]; exact h1, by rw [← htgt a]; exact h2⟩
      · exact Or.inr ⟨by rw [← hsrc a]; exact h1, by rw [← htgt a]; exact h2⟩
  · rintro ⟨huv, hw | ⟨a, ha, hjoin⟩⟩
    · exact ⟨huv, Or.inl hw⟩
    · refine ⟨huv, Or.inr ⟨ι a, ha, ?_⟩⟩
      rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [hsrc a]; exact h1, by rw [htgt a]; exact h2⟩
      · exact Or.inr ⟨by rw [hsrc a]; exact h1, by rw [htgt a]; exact h2⟩

theorem componentCount_res {ξ : Setoid V} {B : E₂ → Bool} (hB : B ∈ ClosedOutside ι)
    (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e) :
    (fgOf E₂ src₂ tgt₂).componentCount ξ B
      = (fgOf E₁ src₁ tgt₁).componentCount ξ (res ι B) := by
  unfold LabelledMultigraph.componentCount
  rw [connectionGraph_res hB hsrc htgt]

end EdgeGrowth

end NoEscape
end FK.InfiniteVolume

namespace FK.InfiniteVolume
namespace NoEscape

open FK.Finite

section EdgeGrowth2

variable {V : Type*} [Fintype V]
variable {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]
variable {src₁ : E₁ → V} {tgt₁ : E₁ → V} {src₂ : E₂ → V} {tgt₂ : E₂ → V}
variable {ι : E₁ → E₂} (hι : Function.Injective ι)

/-- The number of edges of `E₂` outside the embedded copy. -/
noncomputable def extraCard (ι : E₁ → E₂) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : E₂ => ¬ ∃ a : E₁, ι a = e)).card

/-- The canonical extension of a configuration by closed edges off the embedded copy. -/
noncomputable def extA (ι : E₁ → E₂) (A : E₁ → Bool) : E₂ → Bool := by
  classical
  exact fun e => if h : ∃ a : E₁, ι a = e then A (Classical.choose h) else false

lemma extA_apply (hι : Function.Injective ι) {A : E₁ → Bool} (a : E₁) :
    extA ι A (ι a) = A a := by
  classical
  unfold extA
  rw [dif_pos ⟨a, rfl⟩]
  refine congrArg A (hι ?_)
  exact Classical.choose_spec (⟨a, rfl⟩ : ∃ b : E₁, ι b = ι a)

lemma extA_eq_false {A : E₁ → Bool} {e : E₂} (he : ¬ ∃ a : E₁, ι a = e) :
    extA ι A e = false := by
  classical
  unfold extA
  rw [dif_neg he]

lemma res_extA (hι : Function.Injective ι) {A : E₁ → Bool} : res ι (extA ι A) = A := by
  funext a
  exact extA_apply hι a

lemma closedOutside_extA (A : E₁ → Bool) : extA ι A ∈ ClosedOutside ι := by
  intro e he
  exact extA_eq_false he

lemma eq_extA (hι : Function.Injective ι) {B : E₂ → Bool} {A : E₁ → Bool}
    (hB : B ∈ ClosedOutside ι) (hAB : res ι B = A) : B = extA ι A := by
  classical
  funext e
  by_cases he : ∃ a : E₁, ι a = e
  · obtain ⟨a, rfl⟩ := he
    rw [extA_apply hι]
    have h1 := congrFun hAB a
    simpa [res] using h1
  · rw [extA_eq_false he]
    exact hB e he

/-- The Bernoulli edge weight of the closed extension factors through the
embedded copy and a constant factor for the remaining edges. -/
theorem edgeWeight_extA (hι : Function.Injective ι) {p : NNReal} (A : E₁ → Bool) :
    (fgOf E₂ src₂ tgt₂).edgeWeight p (extA ι A)
      = (fgOf E₁ src₁ tgt₁).edgeWeight p A * (1 - p) ^ (extraCard ι) := by
  classical
  set P : E₂ → Prop := fun e => ∃ a : E₁, ι a = e with hP
  have key : (Finset.univ : Finset E₂).prod (fun e => if (extA ι A e = true) then p else 1 - p)
      = ((Finset.univ : Finset E₁).prod (fun a => if (A a = true) then p else 1 - p))
        * (1 - p) ^ (extraCard ι) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset E₂)) (p := P)
      (f := fun e => if (extA ι A e = true) then p else 1 - p)]
    congr 1
    · have himage : (Finset.univ.filter P) = (Finset.univ : Finset E₁).image ι := by
        ext e; simp [hP]
      rw [himage, Finset.prod_image (f := fun e => if (extA ι A e = true) then p else 1 - p)]
      · apply Finset.prod_congr rfl
        intro a _
        rw [extA_apply hι]
      · intro x _ y _ hxy
        exact hι hxy
    · have hc : (Finset.univ.filter (fun e : E₂ => ¬ P e)).card = extraCard ι := rfl
      rw [← hc]
      refine Finset.prod_eq_pow_card ?_
      intro e he
      obtain ⟨-, hne⟩ := Finset.mem_filter.mp he
      rw [extA_eq_false hne]
      rfl
  unfold LabelledMultigraph.edgeWeight
  simp only [fgOf]
  exact key

/-- The exact finite FK weight of the closed extension. -/
theorem fkWeight_extA (hι : Function.Injective ι)
    (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)
    {q p : NNReal} (ξ : Setoid V) (A : E₁ → Bool) :
    (fgOf E₂ src₂ tgt₂).fkWeight q p ξ (extA ι A)
      = (1 - p) ^ (extraCard ι) * (fgOf E₁ src₁ tgt₁).fkWeight q p ξ A := by
  have hcc : (fgOf E₂ src₂ tgt₂).componentCount ξ (extA ι A)
      = (fgOf E₁ src₁ tgt₁).componentCount ξ (res ι (extA ι A)) :=
    componentCount_res (ι := ι) (closedOutside_extA (ι := ι) A) hsrc htgt
  have hr : res ι (extA ι A) = A := res_extA (ι := ι) (A := A) hι
  have hw : (fgOf E₂ src₂ tgt₂).edgeWeight p (extA ι A)
      = (fgOf E₁ src₁ tgt₁).edgeWeight p A * (1 - p) ^ (extraCard ι) :=
    edgeWeight_extA (ι := ι) (A := A) hι
  have hcc' : (fgOf E₂ src₂ tgt₂).componentCount ξ (extA ι A)
      = (fgOf E₁ src₁ tgt₁).componentCount ξ A :=
    hcc.trans (congrArg (fun B => (fgOf E₁ src₁ tgt₁).componentCount ξ B) hr)
  unfold LabelledMultigraph.fkWeight
  rw [hcc', hw,
    mul_comm ((fgOf E₁ src₁ tgt₁).edgeWeight p A) ((1 - p) ^ extraCard ι), mul_assoc]

end EdgeGrowth2

end NoEscape
end FK.InfiniteVolume

namespace FK.InfiniteVolume
namespace NoEscape

open FK.Finite

section EdgeMono

variable {V : Type} [Fintype V] [DecidableEq V]
variable {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂] [DecidableEq E₁] [DecidableEq E₂]
variable {src₁ : E₁ → V} {tgt₁ : E₁ → V} {src₂ : E₂ → V} {tgt₂ : E₂ → V}
variable {ι : E₁ → E₂} (hι : Function.Injective ι)
variable (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)

/-- Two finite measures on a fintype that agree on singletons agree. -/
theorem measure_eq_of_singleton_eq' {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ ν : Measure α} (h : ∀ a, μ {a} = ν {a}) : μ = ν := by
  classical
  ext s _
  have hset : s = ↑(Finset.univ.filter (fun a : α => a ∈ s)) := by
    ext a; simp
  rw [hset]
  rw [← MeasureTheory.sum_measure_singleton, ← MeasureTheory.sum_measure_singleton]
  exact Finset.sum_congr rfl fun a _ => h a

/-- The measure of a set is the sum of its point masses. -/
theorem measure_eq_sum_singleton' {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) (s : Set α) :
    μ s = ∑ a ∈ Finset.univ.filter (fun a : α => a ∈ s), μ {a} := by
  classical
  have hset : s = ↑(Finset.univ.filter (fun a : α => a ∈ s)) := by
    ext a; simp
  rw [hset, ← MeasureTheory.sum_measure_singleton]
  simp

/-- Summing the FK weights over the closed configurations whose restriction lies in
`S` gives the smaller graph's weight sum times the constant Bernoulli factor. -/
theorem fkWeight_closed (hι : Function.Injective ι)
    (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)
    {q p : NNReal} {ξ : Setoid V} {C : E₂ → Bool} (hC : C ∈ ClosedOutside ι) :
    ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ C : ℝ≥0∞)
      = ((1 - p : NNReal) : ℝ≥0∞) ^ (extraCard ι) *
        ((fgOf E₁ src₁ tgt₁).fkWeight q p ξ (res ι C) : ℝ≥0∞) := by
  have hCe : C = extA ι (res ι C) := eq_extA (ι := ι) (A := res ι C) hι hC rfl
  have step1 : (fgOf E₂ src₂ tgt₂).fkWeight q p ξ C
      = (fgOf E₂ src₂ tgt₂).fkWeight q p ξ (extA ι (res ι C)) :=
    congrArg (fun D => (fgOf E₂ src₂ tgt₂).fkWeight q p ξ D) hCe
  calc ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ C : ℝ≥0∞)
      = ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ (extA ι (res ι C)) : ℝ≥0∞) := by rw [step1]
    _ = ((1 - p : NNReal) : ℝ≥0∞) ^ (extraCard ι) *
          ((fgOf E₁ src₁ tgt₁).fkWeight q p ξ (res ι C) : ℝ≥0∞) := by
        exact_mod_cast fkWeight_extA (ι := ι) (A := res ι C) hι hsrc htgt (q := q) (p := p) (ξ := ξ)
/-- Summing the FK weights over the closed configurations whose restriction lies in
`S` gives the smaller graph's weight sum times the constant Bernoulli factor. -/
theorem sum_weight_closed (hι : Function.Injective ι)
    (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)
    {q p : NNReal} {ξ : Setoid V} (S : Set (E₁ → Bool)) :
    ∑ C ∈ Finset.univ.filter (fun C : E₂ → Bool => C ∈ ClosedOutside ι ∧ res ι C ∈ S),
        ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ C : ℝ≥0∞)
      = ((1 - p : NNReal) : ℝ≥0∞) ^ (extraCard ι) *
        ∑ B ∈ Finset.univ.filter (fun B : E₁ → Bool => B ∈ S),
          ((fgOf E₁ src₁ tgt₁).fkWeight q p ξ B : ℝ≥0∞) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun C _ => res ι C) ?_ ?_ ?_ ?_
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    exact hC.2
  · intro C₁ hC₁ C₂ hC₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC₁ hC₂
    have h1 : C₁ = extA ι (res ι C₁) :=
      eq_extA (ι := ι) (A := res ι C₁) hι hC₁.1 rfl
    have h2 : C₂ = extA ι (res ι C₂) :=
      eq_extA (ι := ι) (A := res ι C₂) hι hC₂.1 rfl
    rw [h1, h2, h]
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    refine ⟨extA ι B, ?_, res_extA (ι := ι) (A := B) hι⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨closedOutside_extA (ι := ι) B, by rw [res_extA (ι := ι) (A := B) hι]; exact hB⟩
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    exact fkWeight_closed (ι := ι) hι hsrc htgt hC.1

end EdgeMono

section EdgeMonoFinal

variable {V : Type} [Fintype V] [DecidableEq V]
variable {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂] [DecidableEq E₁] [DecidableEq E₂]
variable {src₁ : E₁ → V} {tgt₁ : E₁ → V} {src₂ : E₂ → V} {tgt₂ : E₂ → V}
variable {ι : E₁ → E₂} (hι : Function.Injective ι)
variable (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)

/-- Mass of a set under the FK law, as a normalized sum of FK weights. -/
theorem mass_eq_ratio {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) {ξ : Setoid V}
    (T : Set (E₂ → Bool)) :
    (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ T
      = (∑ C ∈ cfgFinset (fgOf E₂ src₂ tgt₂) T,
          ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ C : ℝ≥0∞)) /
            (((fgOf E₂ src₂ tgt₂).partitionFunction q p ξ : NNReal) : ℝ≥0∞) := by
  classical
  have hZpos : (0 : NNReal) < (fgOf E₂ src₂ tgt₂).partitionFunction q p ξ :=
    LabelledMultigraph.partitionFunction_pos (fgOf E₂ src₂ tgt₂) (q := q) (p := p) hq hp ξ
  conv_lhs => rw [← coe_cfgFinset (fgOf E₂ src₂ tgt₂) T]
  refine Eq.trans (MeasureTheory.sum_measure_singleton
    (μ := (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ) (s := cfgFinset (fgOf E₂ src₂ tgt₂) T)).symm ?_
  rw [sum_div_eq]
  refine Finset.sum_congr rfl fun C _ => ?_
  refine Eq.trans (LabelledMultigraph.fkMeasure_apply_singleton (fgOf E₂ src₂ tgt₂) hq hp ξ C) ?_
  refine Eq.trans (LabelledMultigraph.fkPMF_apply (fgOf E₂ src₂ tgt₂) hq hp ξ C) ?_
  exact ENNReal.coe_div hZpos.ne'

/-- Mass of a set under the small FK law, as a normalized sum of FK weights. -/
theorem mass_eq_ratio_small {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) {ξ : Setoid V}
    (T : Set (E₁ → Bool)) :
    (fgOf E₁ src₁ tgt₁).fkMeasure hq hp ξ T
      = (∑ C ∈ cfgFinset (fgOf E₁ src₁ tgt₁) T,
          ((fgOf E₁ src₁ tgt₁).fkWeight q p ξ C : ℝ≥0∞)) /
            (((fgOf E₁ src₁ tgt₁).partitionFunction q p ξ : NNReal) : ℝ≥0∞) := by
  classical
  have hZpos : (0 : NNReal) < (fgOf E₁ src₁ tgt₁).partitionFunction q p ξ :=
    LabelledMultigraph.partitionFunction_pos (fgOf E₁ src₁ tgt₁) (q := q) (p := p) hq hp ξ
  conv_lhs => rw [← coe_cfgFinset (fgOf E₁ src₁ tgt₁) T]
  refine Eq.trans (MeasureTheory.sum_measure_singleton
    (μ := (fgOf E₁ src₁ tgt₁).fkMeasure hq hp ξ) (s := cfgFinset (fgOf E₁ src₁ tgt₁) T)).symm ?_
  rw [sum_div_eq]
  refine Finset.sum_congr rfl fun C _ => ?_
  refine Eq.trans (LabelledMultigraph.fkMeasure_apply_singleton (fgOf E₁ src₁ tgt₁) hq hp ξ C) ?_
  refine Eq.trans (LabelledMultigraph.fkPMF_apply (fgOf E₁ src₁ tgt₁) hq hp ξ C) ?_
  exact ENNReal.coe_div hZpos.ne'

/-- The weight-sum identity in `cfgFinset` form. -/
theorem sum_weight_closed_ext (hι : Function.Injective ι)
    (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)
    {q p : NNReal} {ξ : Setoid V} (S : Set (E₁ → Bool)) :
    ∑ C ∈ cfgFinset (fgOf E₂ src₂ tgt₂) (ClosedOutside ι ∩ res ι ⁻¹' S),
        ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ C : ℝ≥0∞)
      = ((1 - p : NNReal) : ℝ≥0∞) ^ (extraCard ι) *
        ∑ B ∈ cfgFinset (fgOf E₁ src₁ tgt₁) S,
          ((fgOf E₁ src₁ tgt₁).fkWeight q p ξ B : ℝ≥0∞) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun C _ => res ι C) ?_ ?_ ?_ ?_
  · intro C hC
    rw [cfgFinset] at hC ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    exact hC.2
  · intro C₁ hC₁ C₂ hC₂ h
    rw [cfgFinset] at hC₁ hC₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC₁ hC₂
    have h1 : C₁ = extA ι (res ι C₁) :=
      eq_extA (ι := ι) (A := res ι C₁) hι hC₁.1 rfl
    have h2 : C₂ = extA ι (res ι C₂) :=
      eq_extA (ι := ι) (A := res ι C₂) hι hC₂.1 rfl
    rw [h1, h2, h]
  · intro B hB
    rw [cfgFinset] at hB ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
    refine ⟨extA ι B, ⟨closedOutside_extA (ι := ι) B, ?_⟩,
      (by exact res_extA (ι := ι) (A := B) hι)⟩
    exact Eq.mpr (congrArg (fun t => t ∈ S) (res_extA (ι := ι) (A := B) hι)) hB
  · intro C hC
    rw [cfgFinset] at hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    exact fkWeight_closed (ι := ι) hι hsrc htgt hC.1

/-- **Free FK measures are increasing in the edge set (given positive association).**
For an injection of edge types with matching endpoints, the law of the smaller graph
is dominated by the larger graph's law on the lifted version of every increasing
event.  This is the finite core of no-mass-escape. -/
theorem fkMeasure_le_of_inj (hι : Function.Injective ι)
    (hsrc : ∀ e, src₂ (ι e) = src₁ e) (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (hp1 : p < 1)
    {ξ : Setoid V} (hPA : PosAssoc q p hq hp)
    {A : Set (E₁ → Bool)} (hA : IsUp A) :
    (fgOf E₁ src₁ tgt₁).fkMeasure hq hp ξ A
      ≤ (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A) := by
  classical
  have hLup : IsUp (res ι ⁻¹' A) := by
    intro B hB C hBC
    simp only [Set.mem_preimage] at hB ⊢
    exact hA _ hB _ fun e => hBC (ι e)
  have hDdown : IsDown (ClosedOutside ι) := by
    intro B hB C hCB e he
    simp only [ClosedOutside] at hB ⊢
    have h1 : C e ≤ B e := hCB e
    rw [hB e he] at h1
    cases hce : C e
    · rfl
    · rw [hce] at h1
      exact absurd h1 (by decide)
  have hPA1 := hPA (fgOf E₂ src₂ tgt₂) ξ (res ι ⁻¹' A) (ClosedOutside ι) hLup hDdown
  set K : ℝ≥0∞ := ((1 - p : NNReal) : ℝ≥0∞) ^ (extraCard ι) with hKdef
  set SA : ℝ≥0∞ := ∑ B ∈ cfgFinset (fgOf E₁ src₁ tgt₁) A,
      ((fgOf E₁ src₁ tgt₁).fkWeight q p ξ B : ℝ≥0∞) with hSAdef
  set SDL : ℝ≥0∞ := ∑ C ∈ cfgFinset (fgOf E₂ src₂ tgt₂) (ClosedOutside ι ∩ res ι ⁻¹' A),
      ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ C : ℝ≥0∞) with hSDLdef
  set SD : ℝ≥0∞ := ∑ C ∈ cfgFinset (fgOf E₂ src₂ tgt₂) (ClosedOutside ι),
      ((fgOf E₂ src₂ tgt₂).fkWeight q p ξ C : ℝ≥0∞) with hSDdef
  set Z₁ : ℝ≥0∞ := (((fgOf E₁ src₁ tgt₁).partitionFunction q p ξ : NNReal) : ℝ≥0∞) with hZ₁def
  set Z₂ : ℝ≥0∞ := (((fgOf E₂ src₂ tgt₂).partitionFunction q p ξ : NNReal) : ℝ≥0∞) with hZ₂def
  have hSDL : SDL = K * SA := by
    rw [hSDLdef, hSAdef, hKdef]
    exact sum_weight_closed_ext (ι := ι) hι hsrc htgt (q := q) (p := p) (ξ := ξ) A
  have hSD : SD = K * Z₁ := by
    rw [hSDdef, hKdef, hZ₁def]
    have h := sum_weight_closed_ext (ι := ι) hι hsrc htgt (q := q) (p := p) (ξ := ξ)
      (Set.univ : Set (E₁ → Bool))
    rw [Set.preimage_univ, Set.inter_univ] at h
    rw [h]
    refine congrArg (fun t => ((1 - p : NNReal) : ℝ≥0∞) ^ (extraCard ι) * t) ?_
    have hsm : (∑ B ∈ cfgFinset (fgOf E₁ src₁ tgt₁) (Set.univ : Set (E₁ → Bool)),
          ((fgOf E₁ src₁ tgt₁).fkWeight q p ξ B : ℝ≥0∞))
        = (((fgOf E₁ src₁ tgt₁).partitionFunction q p ξ : NNReal) : ℝ≥0∞) := by
      rw [partitionFunction_coe (fgOf E₁ src₁ tgt₁) ξ]
      have hcfg : cfgFinset (fgOf E₁ src₁ tgt₁) (Set.univ : Set (E₁ → Bool))
          = (Finset.univ : Finset (fgOf E₁ src₁ tgt₁).Configuration) := by
        apply Finset.coe_inj.mp
        rw [coe_cfgFinset]
        simp
      rw [hcfg]
      exact Finset.sum_congr (univ_congr_fintype _ _) (fun _ _ => rfl)
    exact hsm
  have hmass₁ : (fgOf E₁ src₁ tgt₁).fkMeasure hq hp ξ A = SA / Z₁ := by
    rw [hSAdef, hZ₁def]
    exact mass_eq_ratio_small (E₁ := E₁) (src₁ := src₁) (tgt₁ := tgt₁) (ξ := ξ) hq hp A
  have hmass₂ : (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (ClosedOutside ι ∩ res ι ⁻¹' A)
      = SDL / Z₂ := by
    rw [hSDLdef, hZ₂def]
    exact mass_eq_ratio (E₂ := E₂) (src₂ := src₂) (tgt₂ := tgt₂) (ξ := ξ) hq hp
      (ClosedOutside ι ∩ res ι ⁻¹' A)
  have hmassD : (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (ClosedOutside ι) = SD / Z₂ := by
    rw [hSDdef, hZ₂def]
    exact mass_eq_ratio (E₂ := E₂) (src₂ := src₂) (tgt₂ := tgt₂) (ξ := ξ) hq hp
      (ClosedOutside ι)
  have hK0 : K ≠ 0 := by
    rw [hKdef]
    have hpos : (0 : NNReal) < 1 - p := tsub_pos_of_lt hp1
    have hne : ((1 - p : NNReal) : ℝ≥0∞) ≠ 0 := by
      simp only [Ne, ENNReal.coe_eq_zero]
      exact hpos.ne'
    exact pow_ne_zero _ hne
  have hKt : K ≠ ⊤ := by
    rw [hKdef]; exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hZ₂0 : Z₂ ≠ 0 := by
    rw [hZ₂def, Ne, ENNReal.coe_eq_zero]
    exact (LabelledMultigraph.partitionFunction_pos (fgOf E₂ src₂ tgt₂) (q := q) (p := p)
      hq hp ξ).ne'
  have hZ₂t : Z₂ ≠ ⊤ := by rw [hZ₂def]; exact ENNReal.coe_ne_top
  have hZ₁0 : Z₁ ≠ 0 := by
    rw [hZ₁def, Ne, ENNReal.coe_eq_zero]
    exact (LabelledMultigraph.partitionFunction_pos (fgOf E₁ src₁ tgt₁) (q := q) (p := p)
      hq hp ξ).ne'
  have hZ₁t : Z₁ ≠ ⊤ := by rw [hZ₁def]; exact ENNReal.coe_ne_top
  have hstep : SA ≤ (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A) * Z₁ := by
    have h1 : SDL / Z₂ ≤ ((fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A)) * (SD / Z₂) := by
      rw [Set.inter_comm] at hPA1
      rw [← hmass₂, ← hmassD]
      exact hPA1
    rw [hSDL, hSD] at h1
    have h2 : K * SA ≤ (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A) * (K * Z₁) := by
      have h1' : K * SA / Z₂
          ≤ ((fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A) * (K * Z₁)) / Z₂ := by
        conv_rhs => rw [mul_div_assoc]
        exact h1
      have hthis := (ENNReal.div_le_iff hZ₂0 hZ₂t).mp h1'
      rwa [ENNReal.div_mul_cancel hZ₂0 hZ₂t] at hthis
    have heq : (fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A) * (K * Z₁)
        = K * ((fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A) * Z₁) := by
      rw [mul_comm ((fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A)) (K * Z₁),
        mul_assoc, mul_comm Z₁ ((fgOf E₂ src₂ tgt₂).fkMeasure hq hp ξ (res ι ⁻¹' A)),
        ← mul_assoc]
    exact (ENNReal.mul_le_mul_iff_right hK0 hKt).mp (heq ▸ h2)
  rw [hmass₁, ENNReal.div_le_iff hZ₁0 hZ₁t]
  exact hstep

end EdgeMonoFinal




open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology


/-- **Analytic no-mass-escape passage.**  If the finite-stage laws are monotone in the
box on the connection events (`hmono`, the conclusion of the finite domain-monotonicity
theorem for free random-cluster laws) and the connection events are clopen, increasing
and exhaust the limiting connection event, then no mass escapes: the limsup of the
stage connection masses is bounded by the limiting connection mass.  This is exactly
the `hnoEscape` input of `FK.InfiniteVolume.OneEdgeNoEscape.onePoint_edge_of_noEscape`. -/
theorem noEscape_of_stage_mono {E : Type*} [Countable E]
    (stage : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto stage atTop (𝓝 μ))
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hmono : ∀ m k, m ≤ k →
      (stage m : Measure (Configuration E)) (C m)
        ≤ (stage k : Measure (Configuration E)) (C m)) :
    Filter.limsup (fun k => ((stage k : Measure (Configuration E)) (C k)).toReal) atTop
      ≤ ((μ : Measure (Configuration E)) Cinf).toReal := by
  classical
  have hconv : ∀ m, Tendsto (fun k => ((stage k : Measure (Configuration E)) (C m)).toReal)
      atTop (𝓝 (((μ : Measure (Configuration E)) (C m)).toReal)) :=
    fun m => FK.InfiniteVolume.OneEdgeNoEscape.tendsto_measure_toReal_of_isClopen (hCcl m) hμ
  have hCsub : ∀ k, C k ⊆ Cinf := by
    intro k ω hω
    exact (hCunion ω).mp ⟨k, hω⟩
  have hbound : ∀ k, ((stage k : Measure (Configuration E)) (C k)).toReal
      ≤ ((μ : Measure (Configuration E)) Cinf).toReal := by
    intro k
    have hstep : ((stage k : Measure (Configuration E)) (C k)).toReal
        ≤ ((μ : Measure (Configuration E)) (C k)).toReal := by
      refine le_of_tendsto_of_tendsto tendsto_const_nhds (hconv k) ?_
      filter_upwards [eventually_ge_atTop k] with j hj
      exact ENNReal.toReal_mono (measure_ne_top _ _) (hmono k j hj)
    refine hstep.trans ?_
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hCsub k))
  have hcob : IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) atTop
      (fun k => ((stage k : Measure (Configuration E)) (C k)).toReal) := by
    refine ⟨0, ?_⟩
    intro b hb
    by_contra hlt
    push Not at hlt
    rw [eventually_map] at hb
    obtain ⟨k, hk⟩ := Filter.Eventually.exists (hb.and (Eventually.of_forall fun k =>
      ENNReal.toReal_nonneg))
    linarith [hk.1, hk.2]
  have hbdd : IsBoundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) atTop
      (fun k => ((stage k : Measure (Configuration E)) (C k)).toReal) :=
    ⟨_, eventually_map.mpr (Eventually.of_forall hbound)⟩
  exact (Filter.limsup_le_iff (f := atTop)
    (u := fun k => ((stage k : Measure (Configuration E)) (C k)).toReal)
    (x := ((μ : Measure (Configuration E)) Cinf).toReal) hcob hbdd).mpr
    (fun b hb => Eventually.of_forall fun k => lt_of_le_of_lt (hbound k) hb)

end NoEscape
end FK.InfiniteVolume
