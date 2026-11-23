import FK.ConditionalRate
import FK.ClassicalOne
import FK.MarkovFactorization

/-!
# Actual finite FK/Bernoulli sequential ordered couplings

The pair process uses canonical prefix conditionals for its FK coordinate and
fresh independent bits for its Bernoulli coordinate.  Its finite-prefix
marginals, exact configuration marginals, and pointwise support order are all
proved.  This supplies the concrete sequential ordered pair required before
combining two pairs through their common upper coordinate.
-/

namespace FK.Exploration.FKCoupling

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.Comparison

/-- A labelled multigraph with an explicitly finite-indexed edge type. -/
def finIndexedGraph (V : Type*) [Fintype V] (n : ℕ) (s t : Fin n → V) :
    LabelledMultigraph where
  Vertex := V
  Edge := Fin n
  source := s
  target := t

/-- `p′` in `NNReal`, with its real coercion definitionally available through
this constructor rather than a second incompatible parameter convention. -/
noncomputable def primeNN (q p : NNReal) : NNReal :=
  ⟨max (FK.prime (q : ℝ) (p : ℝ)) 0, le_max_right _ _⟩

lemma coe_primeNN (q p : NNReal) (hq : 0 < q) (hp : p ≤ 1) :
    (primeNN q p : ℝ) = FK.prime (q : ℝ) (p : ℝ) := by
  change max (FK.prime (q : ℝ) (p : ℝ)) 0 = FK.prime (q : ℝ) (p : ℝ)
  exact max_eq_left (FK.prime_nonneg (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp))


noncomputable def upperRateNN (q p : NNReal) : NNReal := max p (primeNN q p)

lemma coe_upperRateNN (q p : NNReal) (hq : 0 < q) (hp : p ≤ 1) :
    (upperRateNN q p : ℝ) = fkHi q p := by
  change max (p : ℝ) ((primeNN q p : NNReal) : ℝ) = fkHi q p
  rw [coe_primeNN q p hq hp]
  rfl


lemma upperRateNN_le_one {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    upperRateNN q p ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_upperRateNN q p hq hp, NNReal.coe_one]
  exact (fkHi_mem_Icc hq hp).2

lemma upperRateNN_pos {q p : NNReal} (hp0 : 0 < p) : 0 < upperRateNN q p :=
  lt_of_lt_of_le hp0 (le_max_left _ _)

lemma upperRateNN_lt_one {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    upperRateNN q p < 1 := by
  rw [← NNReal.coe_lt_coe, coe_upperRateNN q p hq hp1.le, NNReal.coe_one]
  exact fkHi_lt_one hq hp1

/-- Pointwise positivity of the actual finite FK PMF in the interior
parameter range. -/
lemma fkPMF_ne_zero (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (ξ : G.BoundaryPartition)
    (ω : G.Configuration) : G.fkPMF hq hp1.le ξ ω ≠ 0 := by
  rw [LabelledMultigraph.fkPMF_apply]
  exact_mod_cast (div_pos (G.fkWeight_pos hq hp0 hp1 ξ ω)
    (G.partitionFunction_pos hq hp1.le ξ)).ne'

/-- Convert a history back to a finite configuration without any inverse or
length side condition.  Every coordinate outside a short list defaults to
closed, and is never used on histories output by the finite process. -/
def toConfig (n : ℕ) (x : List Bool) : Fin n → Bool :=
  fun i => x.getD i.1 false

lemma toConfig_ofFn {n : ℕ} (ω : Fin n → Bool) : toConfig n (List.ofFn ω) = ω := by
  funext i
  exact getD_ofFn ω i.isLt

/-- One ordered step between a canonical lower prefix law and a fresh upper
Bernoulli law. -/
noncomputable def orderedUpperStep {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (r : NNReal) (hr : r ≤ 1)
    (hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ)) :
    List Bool → List Bool → PMF (Bool × Bool) :=
  fun x _ => (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r hr (hbound x)).dist

/-- The full append-history pair process with fresh Bernoulli upper bits. -/
noncomputable def upperHistoryPair {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (r : NNReal) (hr : r ≤ 1)
    (hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ)) (k : ℕ) :
    PMF (List Bool × List Bool) :=
  extendPair (orderedUpperStep μ hμ r hr hbound) [] [] k

lemma upperHistoryPair_map_fst {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (r : NNReal) (hr : r ≤ 1)
    (hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ)) :
    (upperHistoryPair μ hμ r hr hbound n).map
        (fun z => toConfig n z.1) = μ := by
  let c := fun (x y : List Bool) => boolOrderedCouplingOfLe (canonicalNext μ hμ x) r hr (hbound x)
  have hf : ∀ x y, ((c x y).dist).map Prod.fst = canonicalNext μ hμ x :=
    fun x y => (c x y).map_fst
  have hm := extendPair_map_fst (orderedUpperStep μ hμ r hr hbound)
    (canonicalNext μ hμ) hf [] [] n
  calc
    (upperHistoryPair μ hμ r hr hbound n).map (fun z => toConfig n z.1) =
        ((extendPair (orderedUpperStep μ hμ r hr hbound) [] [] n).map Prod.fst).map
          (toConfig n) := by rw [PMF.map_comp]; rfl
    _ = (extendLower (canonicalNext μ hμ) [] n).map (toConfig n) := by rw [hm]
    _ = ((extendLower (canonicalNext μ hμ) [] n).map (toConfig n)) := rfl
    _ = μ := by
      rw [extendLower_canonicalNext_nil]
      rw [PMF.map_comp]
      have hcomp : toConfig n ∘ List.ofFn = id := by
        funext ω
        exact toConfig_ofFn ω
      rw [hcomp, PMF.map_id]

lemma upperHistoryPair_map_snd {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (r : NNReal) (hr : r ≤ 1)
    (hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ)) :
    (upperHistoryPair μ hμ r hr hbound n).map
        (fun z => toConfig n z.2) =
      (extendLower (fun _ => FKModel.bernoulliPMF r hr) [] n).map (toConfig n) := by
  let c := fun (x y : List Bool) => boolOrderedCouplingOfLe (canonicalNext μ hμ x) r hr (hbound x)
  have hs : ∀ x y, ((c x y).dist).map Prod.snd = FKModel.bernoulliPMF r hr :=
    fun x y => (c x y).map_snd
  have hm := extendPair_map_snd (orderedUpperStep μ hμ r hr hbound)
    (fun _ => FKModel.bernoulliPMF r hr) hs [] [] n
  calc
    (upperHistoryPair μ hμ r hr hbound n).map (fun z => toConfig n z.2) =
        ((extendPair (orderedUpperStep μ hμ r hr hbound) [] [] n).map Prod.snd).map
          (toConfig n) := by rw [PMF.map_comp]; rfl
    _ = (extendLower (fun _ => FKModel.bernoulliPMF r hr) [] n).map (toConfig n) := by
      rw [hm]

lemma upperHistoryPair_ordered {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (r : NNReal) (hr : r ≤ 1)
    (hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ)) (k : ℕ)
    {z : List Bool × List Bool} (hz : z ∈ (upperHistoryPair μ hμ r hr hbound k).support) :
    List.Forall₂ (fun a b : Bool => a ≤ b) z.1 z.2 := by
  apply extendPair_ordered (orderedUpperStep μ hμ r hr hbound) _ List.Forall₂.nil k hz
  intro x y w hw
  exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r hr (hbound x)).ordered w hw

/-- Fresh constant-bit history generation agrees with canonical generation by
any positive law whose exact prefix conditionals are that same constant law. -/
lemma extendLower_const_eq_canonical {n : ℕ} (ν : PMF (Fin n → Bool))
    (hν : ∀ ω, ν ω ≠ 0) (r : NNReal) (hr : r ≤ 1)
    (hbit : ∀ x (hx : x.length < n), nextBit ν hν x hx = FKModel.bernoulliPMF r hr)
    (x : List Bool) (k : ℕ) (hxk : x.length + k = n) :
    extendLower (fun _ => FKModel.bernoulliPMF r hr) x k =
      extendLower (canonicalNext ν hν) x k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have hx : x.length < n := by omega
      simp only [extendLower, canonicalNext, dif_pos hx, hbit x hx]
      congr 1
      funext b
      exact ih (x ++ [b]) (by simp; omega)

/-- Fresh-bit generation has the prescribed exact upper configuration law
whenever its next-prefix conditionals are constant Bernoulli. -/
lemma upperHistoryPair_map_snd_of_nextBit {n : ℕ} (μ ν : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (hν : ∀ ω, ν ω ≠ 0)
    (r : NNReal) (hr : r ≤ 1)
    (hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ))
    (hbit : ∀ x (hx : x.length < n), nextBit ν hν x hx = FKModel.bernoulliPMF r hr) :
    (upperHistoryPair μ hμ r hr hbound n).map (fun z => toConfig n z.2) = ν := by
  rw [upperHistoryPair_map_snd μ hμ r hr hbound]
  rw [extendLower_const_eq_canonical ν hν r hr hbit [] n (by simp)]
  rw [extendLower_canonicalNext_nil]
  rw [PMF.map_comp]
  have hcomp : toConfig n ∘ List.ofFn = id := by
    funext ω
    exact toConfig_ofFn ω
  rw [hcomp, PMF.map_id]

/-- Canonical prefix conditionals of an actual independent labelled-edge
product are its prescribed constant Bernoulli law. -/
theorem nextBit_bernoulliProduct {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    {r : NNReal} (hr0 : 0 < r) (hr1 : r < 1)
    (x : List Bool) (hx : x.length < n) :
    nextBit ((finIndexedGraph V n s t).bernoulliProductPMF hr1.le)
      (by
        let G := finIndexedGraph V n s t
        intro ω
        change (G.bernoulliProductPMF hr1.le) ω ≠ 0
        rw [← G.fkPMF_q_one hr1.le ξ]
        exact fkPMF_ne_zero G zero_lt_one hr0 hr1 ξ ω) x hx =
      FKModel.bernoulliPMF r hr1.le := by
  let G := finIndexedGraph V n s t
  let ν := G.bernoulliProductPMF hr1.le
  let hν : ∀ ω, ν ω ≠ 0 := by
    intro ω
    change (G.bernoulliProductPMF hr1.le) ω ≠ 0
    rw [← G.fkPMF_q_one hr1.le ξ]
    exact fkPMF_ne_zero G zero_lt_one hr0 hr1 ξ ω
  letI : Fintype (Fin n) := G.fintypeEdge
  letI : Fintype (Fin n → Bool) := G.instFintypeConfiguration
  letI : DecidableEq (Fin n) := Classical.decEq _
  let c : Glauber.EdgeConditionals Bool G.Edge :=
    fun _ _ => boolLaw (r : ℝ) ⟨hr0.le, hr1.le⟩
  have hc : Glauber.HasEdgeConditional (Glauber.ofPMF ν) c ⟨x.length, hx⟩ := by
    change Glauber.HasEdgeConditional
      (Glauber.ofPMF (G.bernoulliProductPMF hr1.le)) c ⟨x.length, hx⟩
    rw [show Glauber.ofPMF (G.bernoulliProductPMF hr1.le) = boolProduct (fun _ : Fin n => (r : ℝ))
      (fun _ => ⟨hr0.le, hr1.le⟩) from G.ofPMF_bernoulliProductPMF hr1.le]
    exact boolProduct_hasEdgeConditional (fun _ : Fin n => (r : ℝ))
      (fun _ => ⟨hr0.le, hr1.le⟩) _
  change nextBit (G.bernoulliProductPMF hr1.le) hν x hx = _
  apply eq_of_true_toReal_eq
  rw [@nextBit_true_toReal_eq n G.fintypeEdge (Classical.decEq _)
      (G.bernoulliProductPMF hr1.le) hν x hx c hc (r : ℝ) (by intro off; apply boolLaw_true)]
  rw [FKModel.bernoulliPMF_apply]
  rfl

/-- Pointwise history order descends through `toConfig`. -/
lemma toConfig_le_of_forall₂ {n : ℕ} {x y : List Bool}
    (h : List.Forall₂ (fun a b : Bool => a ≤ b) x y) :
    toConfig n x ≤ toConfig n y := by
  have hget : ∀ i, x.getD i false ≤ y.getD i false := by
    induction h with
    | nil => intro i; exact le_rfl
    | @cons a b lx ly hab _ ih =>
      intro i
      cases i with
      | zero => exact hab
      | succ i => exact ih i
  intro i
  exact hget i.1

/-- The canonical prefix-conditional FK open rate is bounded by the exact
upper Bernoulli rate on every compatible history; invalid overlong histories
have the deterministic closed fallback. -/
lemma fk_upper_nextBound {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (x : List Bool) :
    (canonicalNext ((finIndexedGraph V n s t).fkPMF hq hp1.le ξ)
      (fun ω => fkPMF_ne_zero (finIndexedGraph V n s t) hq hp0 hp1 ξ ω) x true).toReal ≤
      (upperRateNN q p : ℝ) := by
  let G := finIndexedGraph V n s t
  let μ := G.fkPMF hq hp1.le ξ
  let hμ : ∀ ω, μ ω ≠ 0 := fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω
  letI : Fintype (Fin n) := G.fintypeEdge
  letI : Fintype (Fin n → Bool) := G.instFintypeConfiguration
  letI : DecidableEq (Fin n) := Classical.decEq _
  by_cases hx : x.length < n
  · have hc : Glauber.HasEdgeConditional (Glauber.ofPMF μ)
        (fkConditionals G hq hp1.le ξ) ⟨x.length, hx⟩ :=
      fk_hasEdgeConditional G hq hp1.le ξ _
    have hb := @nextBit_true_toReal_le n G.fintypeEdge (Classical.decEq _) μ hμ x hx
      (fkConditionals G hq hp1.le ξ) hc (fkHi q p)
      (fun off => fkRate_le_max G ξ _ off)
    simp only [canonicalNext, dif_pos hx]
    simpa [coe_upperRateNN q p hq hp1.le] using hb
  · simp [canonicalNext, hx]

/-- The actual finite FK/upper-Bernoulli pair law on graph configurations. -/
noncomputable def fkUpperPair {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    PMF ((Fin n → Bool) × (Fin n → Bool)) := by
  let G := finIndexedGraph V n s t
  let μ := G.fkPMF hq hp1.le ξ
  let r := upperRateNN q p
  let hr := upperRateNN_le_one hq hp1.le
  let hμ : ∀ ω, μ ω ≠ 0 := fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω
  let hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ) := by
    intro x
    exact fk_upper_nextBound s t ξ hq hp0 hp1 x
  exact (upperHistoryPair μ hμ r hr hbound n).map
    (fun z => (toConfig n z.1, toConfig n z.2))

/-- The FK marginal is the actual graph law, at the original labelled edges
and arbitrary boundary setoid. -/
theorem fkUpperPair_map_fst {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    (fkUpperPair s t ξ hq hp0 hp1).map Prod.fst =
      (finIndexedGraph V n s t).fkPMF hq hp1.le ξ := by
  unfold fkUpperPair
  dsimp only
  rw [PMF.map_comp]
  exact upperHistoryPair_map_fst _ _ _ _ _

/-- The upper marginal is the exact independent Bernoulli product at
`upperRateNN`. -/
theorem fkUpperPair_map_snd {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    (fkUpperPair s t ξ hq hp0 hp1).map Prod.snd =
      (finIndexedGraph V n s t).bernoulliProductPMF
        (upperRateNN_le_one hq hp1.le) := by
  unfold fkUpperPair
  dsimp only
  rw [PMF.map_comp]
  apply upperHistoryPair_map_snd_of_nextBit
  intro x hx
  exact nextBit_bernoulliProduct s t ξ
    (upperRateNN_pos hp0) (upperRateNN_lt_one hq hp0 hp1) x hx

/-- Every supported pair is pointwise ordered from the FK configuration to
the upper Bernoulli configuration. -/
theorem fkUpperPair_ordered {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    {z : (Fin n → Bool) × (Fin n → Bool)}
    (hz : z ∈ (fkUpperPair s t ξ hq hp0 hp1).support) : z.1 ≤ z.2 := by
  unfold fkUpperPair at hz
  rw [PMF.mem_support_map_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact toConfig_le_of_forall₂ (upperHistoryPair_ordered _ _ _ _ _ _ hw)

/-- Package the explicit FK/upper pair as an ordered coupling structure. -/
noncomputable def fkUpperOrderedCoupling {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    PMF.OrderedCoupling ((finIndexedGraph V n s t).fkPMF hq hp1.le ξ)
      ((finIndexedGraph V n s t).bernoulliProductPMF
        (upperRateNN_le_one hq hp1.le)) where
  dist := fkUpperPair s t ξ hq hp0 hp1
  map_fst := fkUpperPair_map_fst s t ξ hq hp0 hp1
  map_snd := fkUpperPair_map_snd s t ξ hq hp0 hp1
  ordered _ hz := fkUpperPair_ordered s t ξ hq hp0 hp1 hz

/-- Two actual FK configurations with arbitrary boundary setoids and one
common dominating Bernoulli configuration, constructed by joining the two
explicit sequential pairs conditionally on their common upper coordinate. -/
noncomputable def fkOrderedTriple {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ₁ ξ₂ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    PMF ((Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)) :=
  (PMF.OrderedCoupling.glue (fkUpperOrderedCoupling s t ξ₁ hq hp0 hp1)
    (fkUpperOrderedCoupling s t ξ₂ hq hp0 hp1)).dist

/-- The first FK marginal of the ordered triple is exact. -/
theorem fkOrderedTriple_map_fst {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ₁ ξ₂ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    (fkOrderedTriple s t ξ₁ ξ₂ hq hp0 hp1).map (fun z => z.1) =
      (finIndexedGraph V n s t).fkPMF hq hp1.le ξ₁ :=
  (PMF.OrderedCoupling.glue (fkUpperOrderedCoupling s t ξ₁ hq hp0 hp1)
    (fkUpperOrderedCoupling s t ξ₂ hq hp0 hp1)).map_fst

/-- The second FK marginal of the ordered triple is exact. -/
theorem fkOrderedTriple_map_snd {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ₁ ξ₂ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    (fkOrderedTriple s t ξ₁ ξ₂ hq hp0 hp1).map (fun z => z.2.1) =
      (finIndexedGraph V n s t).fkPMF hq hp1.le ξ₂ :=
  (PMF.OrderedCoupling.glue (fkUpperOrderedCoupling s t ξ₁ hq hp0 hp1)
    (fkUpperOrderedCoupling s t ξ₂ hq hp0 hp1)).map_snd

/-- The third marginal is the actual independent Bernoulli product. -/
theorem fkOrderedTriple_map_thd {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ₁ ξ₂ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    (fkOrderedTriple s t ξ₁ ξ₂ hq hp0 hp1).map (fun z => z.2.2) =
      (finIndexedGraph V n s t).bernoulliProductPMF
        (upperRateNN_le_one hq hp1.le) :=
  (PMF.OrderedCoupling.glue (fkUpperOrderedCoupling s t ξ₁ hq hp0 hp1)
    (fkUpperOrderedCoupling s t ξ₂ hq hp0 hp1)).map_thd

/-- Both lower configurations are below the common upper configuration on
every point of support. -/
theorem fkOrderedTriple_ordered {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (ξ₁ ξ₂ : (finIndexedGraph V n s t).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    {z : (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)}
    (hz : z ∈ (fkOrderedTriple s t ξ₁ ξ₂ hq hp0 hp1).support) :
    z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
  exact ⟨(PMF.OrderedCoupling.glue (fkUpperOrderedCoupling s t ξ₁ hq hp0 hp1)
      (fkUpperOrderedCoupling s t ξ₂ hq hp0 hp1)).rel_fst z hz,
    (PMF.OrderedCoupling.glue (fkUpperOrderedCoupling s t ξ₁ hq hp0 hp1)
      (fkUpperOrderedCoupling s t ξ₂ hq hp0 hp1)).rel_snd z hz⟩

end FK.Exploration.FKCoupling
