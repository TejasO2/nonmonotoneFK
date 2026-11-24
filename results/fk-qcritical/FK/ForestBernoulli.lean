import FK.ClassicalOne
import FK.PlanarForestDuality

namespace FK.ForestBernoulli

open scoped BigOperators ENNReal NNReal Classical
open FK.Finite (LabelledMultigraph)

variable {E : Type*} [Fintype E]

/-! ### Counting open labels -/

/-- The number of open labels of a Boolean configuration. -/
def openCount (ω : E → Bool) : ℕ := (Finset.univ.filter (fun e => ω e = true)).card

/-- `openCount` is the repository's `openCard`. -/
lemma openCount_eq_openCard (ω : E → Bool) : openCount ω = FK.FinitePlane.openCard ω := rfl

/-- A product of `a` over the open labels is `a` to the number of open labels. -/
lemma prod_ite_one_pow (ω : E → Bool) (a : NNReal) :
    (∏ e, (if ω e then a else 1)) = a ^ openCount ω := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (s := (Finset.univ : Finset E))
    (p := fun e => ω e = true) (f := fun e => if ω e then a else 1)]
  have h1 : (∏ x ∈ Finset.univ.filter (fun x => ω x = true), (if ω x then a else 1))
      = a ^ openCount ω := by
    rw [openCount,
      show (∏ x ∈ Finset.univ.filter (fun x => ω x = true), (if ω x then a else 1))
          = ∏ x ∈ Finset.univ.filter (fun x => ω x = true), a from by
        refine Finset.prod_congr rfl ?_
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [if_pos hx.2]]
    rw [Finset.prod_const]
  have h2 : (∏ x ∈ Finset.univ.filter (fun x => ¬ (ω x = true)), (if ω x then a else 1)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro x hx
    rw [Finset.mem_filter] at hx
    have hfalse : ω x = false := by cases h : ω x <;> simp_all
    rw [if_neg (by rw [hfalse]; simp)]
  rw [h1, h2, mul_one]

/-! ### The modified edge parameter -/

/-- The FK denominator `p + q(1-p)`. -/
def fkDen (q p : NNReal) : NNReal := p + q * (1 - p)

/-- The modified edge parameter `p / (p + q(1-p))`. -/
noncomputable def fkMod (q p : NNReal) : NNReal := p / fkDen q p

lemma le_fkDen (hp : p ≤ 1) (q : NNReal) : p ≤ fkDen q p := by
  have h : (0 : NNReal) ≤ q * (1 - p) := by positivity
  simp only [fkDen]; linarith

lemma fkDen_pos {q p : NNReal} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) : 0 < fkDen q p :=
  lt_of_lt_of_le hp (le_fkDen hp1.le q)

lemma fkDen_ne_zero {q p : NNReal} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) :
    fkDen q p ≠ 0 := (fkDen_pos hq hp hp1).ne'

lemma fkMod_le_one {q p : NNReal} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) :
    fkMod q p ≤ 1 := by
  have hD := fkDen_pos hq hp hp1
  rw [fkMod, div_le_one hD]
  exact le_fkDen hp1.le q

lemma fkDen_sub {q : NNReal} {p : NNReal} (hp : p ≤ 1) : fkDen q p - p = q * (1 - p) := by
  simp only [fkDen]
  rw [add_tsub_cancel_left]

/-- `q * (D/q) = D`. -/
lemma mul_fkDen_div (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    q * (fkDen q p / q) = fkDen q p :=
  mul_div_cancel₀ _ hq.ne'

/-- `(p/D) * D = p`. -/
lemma fkMod_mul_fkDen (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    fkMod q p * fkDen q p = p := by
  rw [fkMod]
  exact div_mul_cancel₀ p (fkDen_ne_zero hq hp0 hp1)

/-- `(1 - p/D) * D = q(1-p)`. -/
lemma one_sub_fkMod_mul_fkDen (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    ((1 : NNReal) - fkMod q p) * fkDen q p = q * (1 - p) := by
  rw [tsub_mul, one_mul, fkMod_mul_fkDen hq hp0 hp1, fkDen_sub hp1.le]

/-- The one-label identity that absorbs the `q`-factor into the edge parameter:
`p` (open) and `1-p` (closed) are `q`-times the modified Bernoulli masses. -/
lemma one_label_factor {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    (if b then p else 1 - p) =
      (if b then q else 1) * (fkDen q p / q * (if b then fkMod q p else 1 - fkMod q p)) := by
  have hqD := mul_fkDen_div hq hp0 hp1
  cases b
  · simp only [Bool.false_eq_true, ite_false, one_mul]
    have key : fkDen q p / q * ((1 : NNReal) - fkMod q p) * q = (1 - p) * q := by
      calc fkDen q p / q * ((1 : NNReal) - fkMod q p) * q
          = fkDen q p / q * q * ((1 : NNReal) - fkMod q p) := by ring
        _ = fkDen q p * ((1 : NNReal) - fkMod q p) := by rw [div_mul_cancel₀ _ hq.ne']
        _ = ((1 : NNReal) - fkMod q p) * fkDen q p := by ring
        _ = q * (1 - p) := one_sub_fkMod_mul_fkDen hq hp0 hp1
        _ = (1 - p) * q := by ring
    exact (mul_right_cancel₀ hq.ne' key).symm
  · simp only [ite_true]
    have key : q * (fkDen q p / q * fkMod q p) = p := by
      rw [← mul_assoc, hqD, mul_comm (fkDen q p) (fkMod q p)]
      exact fkMod_mul_fkDen hq hp0 hp1
    exact key.symm

/-! ### The affine-component-count theorem -/

/-- Edge weights factor through the modified parameter and the `q`-powers. -/
lemma edgeWeight_eq (G : LabelledMultigraph) (ω : G.Configuration) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.edgeWeight p ω =
      q ^ openCount ω * (fkDen q p / q) ^ (Fintype.card G.Edge) * G.edgeWeight (fkMod q p) ω := by
  rw [LabelledMultigraph.edgeWeight, LabelledMultigraph.edgeWeight]
  rw [show (∏ e, (if ω e then p else 1 - p))
      = ∏ e, ((if ω e then q else 1) *
          (fkDen q p / q * (if ω e then fkMod q p else 1 - fkMod q p))) from
    Finset.prod_congr rfl (fun e _ => one_label_factor hq hp0 hp1 (ω e))]
  rw [Finset.prod_mul_distrib, prod_ite_one_pow]
  rw [show (∏ e, fkDen q p / q * (if ω e then fkMod q p else 1 - fkMod q p))
      = (fkDen q p / q) ^ (Fintype.card G.Edge) *
          ∏ e, (if ω e then fkMod q p else 1 - fkMod q p) from by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]]
  ring

/-- The weighted mass factorization behind the affine theorem. -/
lemma fkWeight_of_affine
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (C : ℕ)
    (hk : ∀ ω : G.Configuration, G.componentCount ξ ω + openCount ω = C)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (ω : G.Configuration) :
    G.fkWeight q p ξ ω =
      q ^ C * (fkDen q p / q) ^ (Fintype.card G.Edge) * G.edgeWeight (fkMod q p) ω := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_eq G ω hq hp0 hp1]
  have hkpow : q ^ C = q ^ openCount ω * q ^ G.componentCount ξ ω := by
    rw [← pow_add]
    congr 1
    have h := hk ω
    omega
  rw [hkpow]
  ring

/-- Exact partition function on a graph with an affine component count:
`Z = q^C * (D/q)^{|E|}` with `D = p + q(1-p)`. -/
theorem partitionFunction_of_affine
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (C : ℕ)
    (hk : ∀ ω : G.Configuration, G.componentCount ξ ω + openCount ω = C)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.partitionFunction q p ξ = q ^ C * (fkDen q p / q) ^ (Fintype.card G.Edge) := by
  classical
  rw [LabelledMultigraph.partitionFunction, Finset.sum_congr rfl (fun ω _ => fkWeight_of_affine G ξ C hk hq hp0 hp1 ω),
    ← Finset.mul_sum,
    LabelledMultigraph.sum_edgeWeight G (p := fkMod q p) (fkMod_le_one hq hp0 hp1), mul_one]

/-- Exact partition function of a free-boundary labelled forest:
`Z = q^{|V|} * (D/q)^{|E|}`. -/
theorem partitionFunction_of_labelledForest
    (G : LabelledMultigraph) (hG : G.IsLabelledForest) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.partitionFunction q p G.freeBoundary =
      q ^ Fintype.card G.Vertex * (fkDen q p / q) ^ (Fintype.card G.Edge) := by
  refine partitionFunction_of_affine G G.freeBoundary (Fintype.card G.Vertex) ?_ hq hp0 hp1
  intro ω
  rw [openCount_eq_openCard]
  exact G.componentCount_add_openCard_of_free_isOpenForest ω
    (G.isOpenForest_of_isLabelledForest hG ω)

/-- **The finite FK law on an affine component count is Bernoulli percolation.**
If every configuration's component count plus its number of open labels is the
constant `C`, the normalized FK law at parameters `(q,p)` is the independent
Bernoulli product with parameter `r = p / (p + q(1-p))`. -/
theorem fkPMF_eq_bernoulliProductPMF_of_affine
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (C : ℕ)
    (hk : ∀ ω : G.Configuration, G.componentCount ξ ω + openCount ω = C)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.fkPMF hq hp1.le ξ =
      G.bernoulliProductPMF (p := fkMod q p) (fkMod_le_one hq hp0 hp1) := by
  classical
  have hZ := partitionFunction_of_affine G ξ C hk hq hp0 hp1
  have hZne : G.partitionFunction q p ξ ≠ 0 := (G.partitionFunction_pos hq hp1.le ξ).ne'
  have hKne : q ^ C * (fkDen q p / q) ^ (Fintype.card G.Edge) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hq.ne') (pow_ne_zero _ ?_)
    exact div_ne_zero (fkDen_ne_zero hq hp0 hp1) hq.ne'
  apply PMF.ext
  intro ω
  rw [LabelledMultigraph.fkPMF_apply, LabelledMultigraph.bernoulliProductPMF_apply]
  have hgoal : G.fkWeight q p ξ ω / G.partitionFunction q p ξ =
      G.edgeWeight (fkMod q p) ω := by
    rw [fkWeight_of_affine G ξ C hk hq hp0 hp1 ω, hZ,
      mul_div_cancel_left₀ (G.edgeWeight (fkMod q p) ω) hKne]
  rw [hgoal]

/-! ### The modified parameter against the paper's notation -/

/-- At `q = 1` the modified parameter is the original one. -/
lemma fkMod_one {p : NNReal} (hp : p ≤ 1) : fkMod 1 p = p := by
  rw [fkMod, fkDen, one_mul, add_tsub_cancel_of_le hp, div_one]

/-- The paper's `fkPrime p q = p / (p + q(1-p))` in real coordinates. -/
lemma fkMod_coe_real {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    ((fkMod q p : NNReal) : ℝ) = (p : ℝ) / ((p : ℝ) + (q : ℝ) * (1 - (p : ℝ))) := by
  have hD : fkDen q p ≠ 0 := fkDen_ne_zero hq hp0 hp1
  have hDcast : ((fkDen q p : NNReal) : ℝ) = (p : ℝ) + (q : ℝ) * (1 - (p : ℝ)) := by
    simp only [fkDen]
    push_cast
    rw [NNReal.coe_sub hp1.le]
    norm_num
  rw [fkMod]
  push_cast
  rw [hDcast]

/-! ### Forests -/

/-- **The finite FK law on a labelled forest with free boundary is Bernoulli
percolation** with parameter `p / (p + q(1-p))`, for every interior `q > 0`. -/
theorem fkPMF_eq_bernoulliProductPMF_of_labelledForest
    (G : LabelledMultigraph) (hG : G.IsLabelledForest) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    G.fkPMF hq hp1.le G.freeBoundary =
      G.bernoulliProductPMF (p := fkMod q p) (fkMod_le_one hq hp0 hp1) := by
  refine fkPMF_eq_bernoulliProductPMF_of_affine G G.freeBoundary
    (Fintype.card G.Vertex) ?_ hq hp0 hp1
  intro ω
  rw [openCount_eq_openCard]
  exact G.componentCount_add_openCard_of_free_isOpenForest ω
    (G.isOpenForest_of_isLabelledForest hG ω)

lemma fkDen_le_one {q p : NNReal} (hp : p ≤ 1) (hq1 : q ≤ 1) : fkDen q p ≤ 1 := by
  have hmul : q * (1 - p) ≤ 1 - p := by
    calc q * (1 - p) ≤ 1 * (1 - p) := by gcongr
      _ = 1 - p := one_mul _
  have hsum : p + (1 - p) = 1 := add_tsub_cancel_of_le hp
  simp only [fkDen]
  linarith

/-- In the antiferromagnetic regime `q ≤ 1` the modified parameter is at least
the original one: the `q`-factor pushes the effective parameter up. -/
lemma le_fkMod_of_q_le_one {q p : NNReal} (hp : p ≤ 1) (hq1 : q ≤ 1) :
    p ≤ fkMod q p := by
  rcases eq_or_ne p 0 with hp0 | hp0
  · subst hp0
    rw [fkMod]
    simp
  · have hppos : 0 < p := pos_iff_ne_zero.mpr hp0
    have hDpos : 0 < fkDen q p := lt_of_lt_of_le hppos (le_fkDen hp q)
    rw [fkMod, le_div_iff₀ hDpos]
    calc p * fkDen q p ≤ p * 1 := by gcongr; exact fkDen_le_one hp hq1
      _ = p := mul_one p


/-- Strict form for `q < 1`: the modified parameter strictly exceeds `p`.  This
is the finite forest form of the `q < 1` enhancement mechanism: the random
cluster law on a forest opens edges more often than independent `p`-percolation. -/
lemma lt_fkMod_of_q_lt_one {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    p < fkMod q p := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq
    rw [fkMod, fkDen, zero_mul, add_zero, div_self hp0.ne']
    exact hp1
  · have hqpos : 0 < q := pos_iff_ne_zero.mpr hq
    have hDpos : 0 < fkDen q p := fkDen_pos hqpos hp0 hp1
    have hsub : 0 < 1 - p := tsub_pos_of_lt hp1
    have hlt : q * (1 - p) < 1 * (1 - p) := mul_lt_mul_of_pos_right hq1 hsub
    have hDlt : fkDen q p < 1 := by
      have hsum : p + (1 - p) = 1 := add_tsub_cancel_of_le hp1.le
      simp only [fkDen]
      rw [one_mul] at hlt
      linarith
    rw [fkMod, lt_div_iff₀ hDpos]
    calc p * fkDen q p < p * 1 := mul_lt_mul_of_pos_left hDlt hp0
      _ = p := mul_one p

/-! ### A non-vacuous instance: the single labelled edge -/

/-- The graph with two vertices and one labelled edge joining them. -/
abbrev twoV : LabelledMultigraph where
  Vertex := Fin 2
  Edge := Fin 1
  source := fun _ => 0
  target := fun _ => 1

lemma twoV_comp_allClosed :
    twoV.componentCount twoV.freeBoundary twoV.allClosed = 2 := by
  rw [LabelledMultigraph.componentCount_free_allClosed]
  simp

lemma twoV_comp_allOpen :
    twoV.componentCount twoV.freeBoundary twoV.allOpen = 1 := by
  refine FK.Finite.LabelledMultigraph.componentCount_eq_one_of_preconnected _ _ _ 0 ?_
  intro x y
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · have h0 : x = 0 ∨ x = 1 := by fin_cases x <;> simp
    have h1 : y = 0 ∨ y = 1 := by fin_cases y <;> simp
    have hadj : (twoV.connectionGraph twoV.freeBoundary twoV.allOpen).Adj 0 1 := by
      refine ⟨by decide, Or.inr ⟨(0 : Fin 1), rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    have h01 : (twoV.connectionGraph twoV.freeBoundary twoV.allOpen).Reachable 0 1 :=
      SimpleGraph.Adj.reachable hadj
    rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl
    · exact absurd rfl hxy
    · exact h01
    · exact h01.symm
    · exact absurd rfl hxy

lemma twoV_openCount_allOpen : openCount twoV.allOpen = 1 := by
  simp [openCount, LabelledMultigraph.allOpen]

lemma twoV_openCount_allClosed : openCount twoV.allClosed = 0 := by
  simp [openCount, LabelledMultigraph.allClosed]

lemma twoV_affine (ω : twoV.Configuration) :
    twoV.componentCount twoV.freeBoundary ω + openCount ω = 2 := by
  have hω : ω = twoV.allOpen ∨ ω = twoV.allClosed := by
    by_cases h : ω (0 : Fin 1) = true
    · left; funext e; fin_cases e; simpa [LabelledMultigraph.allOpen] using h
    · right
      funext e
      fin_cases e
      simpa [LabelledMultigraph.allClosed] using h
  rcases hω with h | h
  · subst h
    rw [twoV_comp_allOpen, twoV_openCount_allOpen]
  · subst h
    rw [twoV_comp_allClosed, twoV_openCount_allClosed]

/-- The actual finite FK law on the single labelled edge is the Bernoulli law
with parameter `p / (p + q(1-p))`, at every interior `q > 0`. -/
theorem twoV_fkPMF_eq_bernoulliProductPMF {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    twoV.fkPMF hq hp1.le twoV.freeBoundary =
      twoV.bernoulliProductPMF (p := fkMod q p) (fkMod_le_one hq hp0 hp1) :=
  fkPMF_eq_bernoulliProductPMF_of_affine twoV twoV.freeBoundary 2 twoV_affine hq hp0 hp1

/-- The open mass of the single-edge FK law is exactly `p / (p + q(1-p))`. -/
theorem twoV_fkPMF_open {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    twoV.fkPMF hq hp1.le twoV.freeBoundary (fun _ => true) = (fkMod q p : ℝ≥0∞) := by
  rw [twoV_fkPMF_eq_bernoulliProductPMF hq hp0 hp1,
    LabelledMultigraph.bernoulliProductPMF_apply]
  simp [LabelledMultigraph.edgeWeight]

/-- Mass form of the forest identity: every configuration has exactly the
modified Bernoulli mass. -/
theorem fkPMF_apply_of_labelledForest
    (G : LabelledMultigraph) (hG : G.IsLabelledForest) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (ω : G.Configuration) :
    G.fkPMF hq hp1.le G.freeBoundary ω = (G.edgeWeight (fkMod q p) ω : ℝ≥0∞) := by
  rw [fkPMF_eq_bernoulliProductPMF_of_labelledForest G hG hq hp0 hp1,
    LabelledMultigraph.bernoulliProductPMF_apply]

/-- Consistency with the classical `q = 1` identity `fkPMF_q_one`: at `q = 1` the
affine-component-count theorem returns the Bernoulli law with parameter `p`. -/
theorem fkPMF_q_one_of_affine (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    (C : ℕ) (hk : ∀ ω : G.Configuration, G.componentCount ξ ω + openCount ω = C)
    {p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) :
    G.fkPMF (q := 1) zero_lt_one hp1.le ξ = G.bernoulliProductPMF hp1.le := by
  have h := fkPMF_eq_bernoulliProductPMF_of_affine G ξ C hk zero_lt_one hp0 hp1
  apply PMF.ext
  intro ω
  rw [show G.fkPMF (q := 1) zero_lt_one hp1.le ξ ω =
      (G.edgeWeight (fkMod 1 p) ω : ℝ≥0∞) from by
    rw [h, LabelledMultigraph.bernoulliProductPMF_apply]]
  rw [fkMod_one hp1.le, LabelledMultigraph.bernoulliProductPMF_apply]


/-! ### The affine hypothesis is not automatic: the two-edge parallel cycle -/

/-- In the all-open configuration the two parallel edges join the two vertices. -/
lemma twoEdgeCycle_comp_allOpen :
    FK.Finite.LabelledMultigraph.twoEdgeCycle.componentCount
      FK.Finite.LabelledMultigraph.twoEdgeCycle.freeBoundary
      FK.Finite.LabelledMultigraph.twoEdgeCycle.allOpen = 1 := by
  refine FK.Finite.LabelledMultigraph.componentCount_eq_one_of_preconnected _ _ _ false ?_
  intro x y
  have hadj : (FK.Finite.LabelledMultigraph.twoEdgeCycle.connectionGraph
      FK.Finite.LabelledMultigraph.twoEdgeCycle.freeBoundary
      FK.Finite.LabelledMultigraph.twoEdgeCycle.allOpen).Adj false true := by
    refine ⟨(fun h => Bool.noConfusion h), Or.inr ⟨true, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  have h01 := SimpleGraph.Adj.reachable hadj
  cases x <;> cases y
  · exact SimpleGraph.Reachable.refl _
  · exact h01
  · exact h01.symm
  · exact SimpleGraph.Reachable.refl _

lemma twoEdgeCycle_comp_allClosed :
    FK.Finite.LabelledMultigraph.twoEdgeCycle.componentCount
      FK.Finite.LabelledMultigraph.twoEdgeCycle.freeBoundary
      FK.Finite.LabelledMultigraph.twoEdgeCycle.allClosed = 2 := by
  rw [LabelledMultigraph.componentCount_free_allClosed]
  simp [FK.Finite.LabelledMultigraph.twoEdgeCycle]

lemma twoEdgeCycle_openCount_allOpen :
    openCount (FK.Finite.LabelledMultigraph.twoEdgeCycle.allOpen) = 2 := by
  rw [openCount_eq_openCard, LabelledMultigraph.openCard_allOpen, ← Nat.card_eq_fintype_card]
  simp [FK.Finite.LabelledMultigraph.twoEdgeCycle]

lemma twoEdgeCycle_openCount_allClosed :
    openCount (FK.Finite.LabelledMultigraph.twoEdgeCycle.allClosed) = 0 := by
  simp [openCount, FK.Finite.LabelledMultigraph.twoEdgeCycle, LabelledMultigraph.allClosed]

/-- **The affine hypothesis of the forest theorem is not vacuous and not
automatic.**  On the two-edge parallel cycle the component count is *not*
affine in the number of open labels: the all-closed configuration has
`2 + 0 = 2` while the all-open configuration has `1 + 2 = 3`.  Hence the
`q`-factor cannot be absorbed into an edge parameter there, in contrast with
every labelled forest, where it can. -/
theorem twoEdgeCycle_not_affine :
    ¬ ∃ C : ℕ, ∀ ω : FK.Finite.LabelledMultigraph.twoEdgeCycle.Configuration,
      FK.Finite.LabelledMultigraph.twoEdgeCycle.componentCount
        FK.Finite.LabelledMultigraph.twoEdgeCycle.freeBoundary ω + openCount ω = C := by
  rintro ⟨C, hC⟩
  have h1 := hC FK.Finite.LabelledMultigraph.twoEdgeCycle.allOpen
  have h2 := hC FK.Finite.LabelledMultigraph.twoEdgeCycle.allClosed
  rw [twoEdgeCycle_comp_allOpen, twoEdgeCycle_openCount_allOpen] at h1
  rw [twoEdgeCycle_comp_allClosed, twoEdgeCycle_openCount_allClosed] at h2
  omega

/-- Strict enhancement instantiated: on the single-edge graph, `q < 1` makes the
edge strictly more likely to be open than under independent `p`-percolation. -/
theorem twoV_fkPMF_open_gt {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : q < 1) :
    (p : ℝ≥0∞) < twoV.fkPMF hq hp1.le twoV.freeBoundary (fun _ => true) := by
  rw [twoV_fkPMF_open hq hp0 hp1]
  exact_mod_cast lt_fkMod_of_q_lt_one hp0 hp1 hq1


end FK.ForestBernoulli
