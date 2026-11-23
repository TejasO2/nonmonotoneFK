import FK.FiniteConditional
import FK.OrderedFinite

/-!
# Classical stochastic comparisons for finite FK measures

Bool-valued adapters for the finite Glauber machinery and exact conditional
factorizations for independent products and the actual finite FK PMF.
-/

namespace FK.Finite.Comparison

noncomputable section
open scoped Classical BigOperators ENNReal

open Set Filter
open OpenPath
open FK.FiniteFiber
open FK.Finite.Conditional
open FK.Finite.LabelledMultigraph

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A Bool-valued Bernoulli law, with the open coordinate `true`. -/
def boolLaw (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : OpenPath.FinProb Bool where
  mass b := if b then r else 1 - r
  mass_nonneg b := by
    cases b <;> simp [hr.1, sub_nonneg.mpr hr.2]
  sum_mass := by simp

@[simp] lemma boolLaw_true (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (boolLaw r hr).mass true = r := by simp [boolLaw]

@[simp] lemma boolLaw_false (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (boolLaw r hr).mass false = 1 - r := by simp [boolLaw]

lemma boolLaw_pos (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (b : Bool) :
    0 < (boolLaw r ⟨hr0.le, hr1.le⟩).mass b := by
  change 0 < (if b then r else 1 - r)
  cases b <;> simp [hr0, hr1]

/-- Independent Bool-valued edge variables. -/
noncomputable def boolProduct (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1) :
    OpenPath.FinProb (E → Bool) :=
  OpenPath.FinProb.pi (fun e => boolLaw (r e) (hr e))

/-- Uniform positive clock law on a nonempty finite edge set. -/
noncomputable def uniformClock (E : Type*) [Fintype E] [Nonempty E] :
    OpenPath.FinProb E where
  mass _ := (Fintype.card E : ℝ)⁻¹
  mass_nonneg _ := inv_nonneg.mpr (by positivity)
  sum_mass := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card E : ℝ) ≠ 0 := by positivity
    field_simp

omit [DecidableEq E] in
lemma uniformClock_pos [Nonempty E] (e : E) : 0 < (uniformClock E).mass e := by
  change 0 < (Fintype.card E : ℝ)⁻¹
  positivity

/-- The full configuration whose off-edge restriction is `off` and whose edge
bit is closed. -/
def fullOff (e : E) (off : Glauber.OffConfig Bool E e) : E → Bool :=
  (Glauber.configSplit Bool e).symm (off, false)

omit [Fintype E] in
lemma fullOff_apply (e : E) (off : Glauber.OffConfig Bool E e) :
    (Glauber.configSplit Bool e (fullOff e off)).1 = off := by
  simp [fullOff]

lemma recombine_off (e : E) (off : Glauber.OffConfig Bool E e) (b : Bool) :
    (Glauber.configSplit Bool e).symm (off, b) =
      Function.update (fullOff e off) e b := by
  have h := Glauber.configSplit_symm_update (B := Bool) e (fullOff e off) b
  simpa only [fullOff_apply] using h

lemma outsideMassConj_eq_sum_update (μ : OpenPath.FinProb (E → Bool))
    (e : E) (off : Glauber.OffConfig Bool E e) :
    Glauber.outsideMassConj (Glauber.configSplit Bool e) μ off =
      μ.mass (Function.update (fullOff e off) e false) +
        μ.mass (Function.update (fullOff e off) e true) := by
  unfold Glauber.outsideMassConj
  simp_rw [recombine_off e off]
  simp [add_comm]

/-- Product of all but one independent factor. -/
def offProductMass (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1)
    (e : E) (ω : E → Bool) : ℝ :=
  ∏ a ∈ Finset.univ.erase e, (boolLaw (r a) (hr a)).mass (ω a)

lemma boolProduct_update_mass (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1)
    (e : E) (ω : E → Bool) (b : Bool) :
    (boolProduct r hr).mass (Function.update ω e b) =
      (boolLaw (r e) (hr e)).mass b * offProductMass r hr e ω := by
  unfold boolProduct offProductMass
  rw [OpenPath.FinProb.pi_mass, ← Finset.mul_prod_erase Finset.univ
    (fun a => (boolLaw (r a) (hr a)).mass (Function.update ω e b a))
    (Finset.mem_univ e)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]

lemma boolProduct_outside (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1)
    (e : E) (off : Glauber.OffConfig Bool E e) :
    Glauber.outsideMassConj (Glauber.configSplit Bool e) (boolProduct r hr) off =
      offProductMass r hr e (fullOff e off) := by
  rw [outsideMassConj_eq_sum_update, boolProduct_update_mass, boolProduct_update_mass]
  simp only [boolLaw_false, boolLaw_true]
  ring

/-- Independent products have the expected constant conditional law on every
edge, without any mass positivity side condition. -/
theorem boolProduct_hasEdgeConditional (r : E → ℝ)
    (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1) (e : E) :
    Glauber.HasEdgeConditional (boolProduct r hr)
      (fun e _ => boolLaw (r e) (hr e)) e := by
  intro off b
  rw [recombine_off, boolProduct_update_mass, boolProduct_outside]
  ring

/-- The exact FK open threshold on an off-edge configuration. -/
def fkRate (G : LabelledMultigraph) (q p : NNReal) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) : ℝ :=
  if endpointsConnectedWithout G ξ e (fullOff e off) then (p : ℝ)
    else FK.prime (q : ℝ) (p : ℝ)

lemma fkRate_mem_Icc (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) :
    fkRate G q p ξ e off ∈ Set.Icc (0 : ℝ) 1 := by
  unfold fkRate
  split_ifs
  · exact ⟨by positivity, by exact_mod_cast hp⟩
  · exact FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)

/-- The FK singleton conditional family required by the Glauber machinery. -/
noncomputable def fkConditionals (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    Glauber.EdgeConditionals Bool G.Edge :=
  fun e off => boolLaw (fkRate G q p ξ e off) (fkRate_mem_Icc G hq hp ξ e off)

lemma fkRate_ge_min (G : LabelledMultigraph) {q p : NNReal}
    (ξ : G.BoundaryPartition) (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) :
    min (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) ≤ fkRate G q p ξ e off := by
  unfold fkRate
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

lemma fkRate_le_max (G : LabelledMultigraph) {q p : NNReal}
    (ξ : G.BoundaryPartition) (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) :
    fkRate G q p ξ e off ≤ max (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) := by
  unfold fkRate
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma prime_pos_interior {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < FK.prime (q : ℝ) (p : ℝ) :=
  FK.prime_pos (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1.le)

lemma prime_lt_one_interior {q p : NNReal} (hq : 0 < q) (hp1 : p < 1) :
    FK.prime (q : ℝ) (p : ℝ) < 1 := by
  have hd : (p : ℝ) + (q : ℝ) * (1 - (p : ℝ)) ≠ 0 :=
    (FK.denominator_pos (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1.le)).ne'
  rw [FK.prime_eq_one_sub_dual hd]
  have hdpos : 0 < FK.dual (q : ℝ) (p : ℝ) :=
    FK.dual_pos (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1)
  linarith

lemma fkRate_pos_interior (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) : 0 < fkRate G q p ξ e off := by
  unfold fkRate
  split_ifs
  · exact_mod_cast hp0
  · exact prime_pos_interior hq hp0 hp1

lemma fkRate_lt_one_interior (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp1 : p < 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) : fkRate G q p ξ e off < 1 := by
  unfold fkRate
  split_ifs
  · exact_mod_cast hp1
  · exact prime_lt_one_interior hq hp1

lemma fkFinProb_mass (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) (ω : G.Configuration) :
    (Glauber.ofPMF (G.fkPMF hq hp ξ)).mass ω =
      (G.fkWeight q p ξ ω : ℝ) / (G.partitionFunction q p ξ : ℝ) := by
  change (G.fkPMF hq hp ξ ω).toReal = _
  rw [LabelledMultigraph.fkPMF_apply]
  simp only [ENNReal.coe_toReal, NNReal.coe_div]

lemma fk_outsideMassConj (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) :
    Glauber.outsideMassConj (Glauber.configSplit Bool e)
        (Glauber.ofPMF (G.fkPMF hq hp ξ)) off =
      (G.fkWeight q p ξ (withEdge e false (fullOff e off)) : ℝ) /
          (G.partitionFunction q p ξ : ℝ) +
        (G.fkWeight q p ξ (withEdge e true (fullOff e off)) : ℝ) /
          (G.partitionFunction q p ξ : ℝ) := by
  rw [outsideMassConj_eq_sum_update]
  simp only [fkFinProb_mass, FiniteFiber.withEdge]

lemma fk_open_conditional_factor_connected (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e)
    (hconn : endpointsConnectedWithout G ξ e (fullOff e off)) :
    (Glauber.ofPMF (G.fkPMF hq hp ξ)).mass
        (Function.update (fullOff e off) e true) =
      Glauber.outsideMassConj (Glauber.configSplit Bool e)
        (Glauber.ofPMF (G.fkPMF hq hp ξ)) off * (p : ℝ) := by
  rw [fkFinProb_mass, fk_outsideMassConj]
  let c : NNReal := offEdgeWeight G p e (fullOff e off) *
    q ^ G.componentCount ξ (withEdge e false (fullOff e off))
  have hopen : G.fkWeight q p ξ (withEdge e true (fullOff e off)) = p * c := by
    dsimp [c]
    exact fkWeight_open_eq_of_connected G q p ξ e (fullOff e off) hconn
  have hclosed : G.fkWeight q p ξ (withEdge e false (fullOff e off)) = (1 - p) * c := by
    dsimp [c]
    exact fkWeight_closed_eq_of_connected G q p ξ e (fullOff e off)
  simp only [FiniteFiber.withEdge] at hopen hclosed ⊢
  by_cases hc : c = 0
  · simp [hopen, hclosed, hc]
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hZ : (G.partitionFunction q p ξ : ℝ) ≠ 0 := by
      exact_mod_cast (G.partitionFunction_pos hq hp ξ).ne'
    rw [hopen, hclosed]
    simp only [NNReal.coe_mul, NNReal.coe_sub hp, NNReal.coe_one]
    field_simp [hZ, hc']
    ring

lemma fk_open_conditional_factor_not_connected (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e)
    (hconn : ¬ endpointsConnectedWithout G ξ e (fullOff e off)) :
    (Glauber.ofPMF (G.fkPMF hq hp ξ)).mass
        (Function.update (fullOff e off) e true) =
      Glauber.outsideMassConj (Glauber.configSplit Bool e)
        (Glauber.ofPMF (G.fkPMF hq hp ξ)) off * FK.prime (q : ℝ) (p : ℝ) := by
  rw [fkFinProb_mass, fk_outsideMassConj]
  let c : NNReal := offEdgeWeight G p e (fullOff e off) *
    q ^ G.componentCount ξ (withEdge e true (fullOff e off))
  have hopen : G.fkWeight q p ξ (withEdge e true (fullOff e off)) = p * c := by
    dsimp [c]
    exact fkWeight_open_eq_of_not_connected G q p ξ e (fullOff e off)
  have hclosed : G.fkWeight q p ξ (withEdge e false (fullOff e off)) =
      q * (1 - p) * c := by
    dsimp [c]
    exact fkWeight_closed_eq_of_not_connected G q p ξ e (fullOff e off) hconn
  simp only [FiniteFiber.withEdge] at hopen hclosed ⊢
  by_cases hc : c = 0
  · simp [hopen, hclosed, hc]
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hZ : (G.partitionFunction q p ξ : ℝ) ≠ 0 := by
      exact_mod_cast (G.partitionFunction_pos hq hp ξ).ne'
    have hd : (p : ℝ) + (q : ℝ) * (1 - (p : ℝ)) ≠ 0 :=
      (FK.denominator_pos (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)).ne'
    rw [hopen, hclosed]
    simp only [NNReal.coe_mul, NNReal.coe_sub hp, NNReal.coe_one]
    unfold FK.prime
    field_simp [hZ, hc', hd]
    ring

lemma fk_open_conditional_factor (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e) :
    (Glauber.ofPMF (G.fkPMF hq hp ξ)).mass
        (Function.update (fullOff e off) e true) =
      Glauber.outsideMassConj (Glauber.configSplit Bool e)
        (Glauber.ofPMF (G.fkPMF hq hp ξ)) off * fkRate G q p ξ e off := by
  by_cases hconn : endpointsConnectedWithout G ξ e (fullOff e off)
  · rw [fkRate, ite_eq_left hconn]
    exact fk_open_conditional_factor_connected G hq hp ξ e off hconn
  · rw [fkRate, ite_eq_right hconn]
    exact fk_open_conditional_factor_not_connected G hq hp ξ e off hconn

/-- The actual finite FK law has exactly the singleton conditional family of
Section 3, even on zero-mass off-edge fibers. -/
theorem fk_hasEdgeConditional (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) (e : G.Edge) :
    Glauber.HasEdgeConditional (Glauber.ofPMF (G.fkPMF hq hp ξ))
      (fkConditionals G hq hp ξ) e := by
  intro off b
  let μ := Glauber.ofPMF (G.fkPMF hq hp ξ)
  let M := Glauber.outsideMassConj (Glauber.configSplit Bool e) μ off
  have hout : M = μ.mass (Function.update (fullOff e off) e false) +
      μ.mass (Function.update (fullOff e off) e true) :=
    outsideMassConj_eq_sum_update μ e off
  have ho : μ.mass (Function.update (fullOff e off) e true) = M * fkRate G q p ξ e off :=
    fk_open_conditional_factor G hq hp ξ e off
  cases b with
  | false =>
      change μ.mass ((Glauber.configSplit Bool e).symm (off, false)) =
        M * (fkConditionals G hq hp ξ e off).mass false
      rw [recombine_off]
      change _ = M * (1 - fkRate G q p ξ e off)
      calc
        μ.mass (Function.update (fullOff e off) e false) =
            M - μ.mass (Function.update (fullOff e off) e true) := by rw [hout]; ring
        _ = M * (1 - fkRate G q p ξ e off) := by rw [ho]; ring
  | true =>
      change μ.mass ((Glauber.configSplit Bool e).symm (off, true)) =
        M * (fkConditionals G hq hp ξ e off).mass true
      rw [recombine_off]
      exact ho

/-- The monotone coupling of two Bool laws, with no mass on `(true,false)`. -/
def boolPair (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    OpenPath.FinProb (Bool × Bool) where
  mass
    | (false, false) => 1 - z
    | (false, true) => z - y
    | (true, false) => 0
    | (true, true) => y
  mass_nonneg x := by
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> simp [hy, hyz, hz, sub_nonneg]
  sum_mass := by
    simp only [Fintype.sum_prod_type]
    simp

lemma boolPair_fst (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (boolPair y z hy hyz hz).map Prod.fst =
      boolLaw y ⟨hy, hyz.trans hz⟩ := by
  apply OpenPath.FinProb.ext
  intro b
  cases b <;> simp [OpenPath.FinProb.mass_map, boolPair, boolLaw,
    Fintype.sum_prod_type]

lemma boolPair_snd (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (boolPair y z hy hyz hz).map Prod.snd =
      boolLaw z ⟨hy.trans hyz, hz⟩ := by
  apply OpenPath.FinProb.ext
  intro b
  cases b <;> simp [OpenPath.FinProb.mass_map, boolPair, boolLaw,
    Fintype.sum_prod_type]

lemma boolPair_ordered (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1)
    {x : Bool × Bool} (hx : (boolPair y z hy hyz hz).mass x ≠ 0) : x.1 ≤ x.2 := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> simp_all [boolPair]

/-- Ordered conditional bit laws for the ordered-update adapter. -/
def boolOrderedCoupling (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    OpenPath.FinProb.OrderedCoupling (boolLaw y ⟨hy, hyz.trans hz⟩)
      (boolLaw z ⟨hy.trans hyz, hz⟩) where
  law := boolPair y z hy hyz hz
  fst := boolPair_fst y z hy hyz hz
  snd := boolPair_snd y z hy hyz hz
  ordered _x hx := boolPair_ordered y z hy hyz hz hx

/-- Lower and upper classical comparison parameters. -/
noncomputable def fkLo (q p : NNReal) : ℝ := min (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
noncomputable def fkHi (q p : NNReal) : ℝ := max (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))

lemma fkLo_mem_Icc {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    fkLo q p ∈ Set.Icc (0 : ℝ) 1 := by
  have hp' : FK.prime (q : ℝ) (p : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)
  exact ⟨le_min (by positivity) hp'.1,
    (min_le_left _ _).trans (by exact_mod_cast hp)⟩

lemma fkHi_mem_Icc {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    fkHi q p ∈ Set.Icc (0 : ℝ) 1 := by
  have hp' : FK.prime (q : ℝ) (p : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  exact ⟨hp0.trans (le_max_left (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))),
    max_le (by exact_mod_cast hp) hp'.2⟩

lemma fkLo_pos {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < fkLo q p := by
  exact lt_min (by exact_mod_cast hp0) (prime_pos_interior hq hp0 hp1)

lemma fkLo_lt_one {q p : NNReal} (hp1 : p < 1) : fkLo q p < 1 := by
  exact (min_le_left _ _).trans_lt (by exact_mod_cast hp1)

lemma fkHi_pos {q p : NNReal} (hp0 : 0 < p) : 0 < fkHi q p := by
  exact (show (0 : ℝ) < (p : ℝ) by exact_mod_cast hp0).trans_le (le_max_left _ _)

lemma fkHi_lt_one {q p : NNReal} (hq : 0 < q) (hp1 : p < 1) : fkHi q p < 1 := by
  exact max_lt (by exact_mod_cast hp1) (prime_lt_one_interior hq hp1)

lemma mixture_invariant_of_conditionals (π : OpenPath.FinProb (E → Bool))
    (c : Glauber.EdgeConditionals Bool E)
    (hc : ∀ e, Glauber.HasEdgeConditional π c e)
    (ρ : OpenPath.FinProb E) :
    Glauber.Invariant π (Glauber.mixture ρ (Glauber.edgeUpdate c)) := by
  apply Glauber.mixture_invariant
  intro e
  exact Glauber.edgeUpdate_invariant π c (hc e)

lemma mixture_eq_modifiedJump (ρ : OpenPath.FinProb E)
    (c : Glauber.EdgeConditionals Bool E) :
    Glauber.mixture ρ (Glauber.edgeUpdate c) = Glauber.modifiedJump ρ c ∅ [] := by
  unfold Glauber.modifiedJump
  congr 1
  funext e a
  simp [Glauber.blockUpdate, Glauber.blockCoordinates, Glauber.sweep, Glauber.seq,
    Glauber.FinProb.bind_dirac_right]

/-- Convergence of a full-support, singleton heat-bath chain to its exact
stationary law, from any initial law. -/
theorem mixture_tendsto [Nonempty E] (μ π : OpenPath.FinProb (E → Bool))
    (c : Glauber.EdgeConditionals Bool E)
    (hc : ∀ e, Glauber.HasEdgeConditional π c e)
    (hbit : ∀ e off b, 0 < (c e off).mass b)
    (ρ : OpenPath.FinProb E) (hρ : ∀ e, 0 < ρ.mass e)
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    OpenPath.FinProb.LawTendsto Filter.atTop
      (fun n => μ.bind (Glauber.iterate (Glauber.mixture ρ (Glauber.edgeUpdate c)) n)) π := by
  let e₀ : E := Classical.choice (inferInstance : Nonempty E)
  have hN : 0 < schedule.length := List.length_pos_of_mem (hschedule e₀)
  have hpos : ∀ a b, 0 <
      (Glauber.iterate (Glauber.mixture ρ (Glauber.edgeUpdate c)) schedule.length a).mass b := by
    intro a b
    simpa only [mixture_eq_modifiedJump, Glauber.FinProb.bind_dirac] using
      Glauber.modifiedJump_iterate_pos c hbit ρ hρ ∅ [] schedule hschedule a b
  exact Glauber.tendsto_bind_iterate_of_positive_power μ π
    (Glauber.mixture ρ (Glauber.edgeUpdate c))
    (mixture_invariant_of_conditionals π c hc ρ) hN hpos

/-- Ordered singleton conditional laws give stochastic domination between the
corresponding full-support stationary configuration laws. -/
theorem stochLe_of_ordered_conditionals [Nonempty E]
    (π₀ π₁ : OpenPath.FinProb (E → Bool))
    (c₀ c₁ : Glauber.EdgeConditionals Bool E)
    (hc₀ : ∀ e, Glauber.HasEdgeConditional π₀ c₀ e)
    (hc₁ : ∀ e, Glauber.HasEdgeConditional π₁ c₁ e)
    (s : ∀ e off₀ off₁, OpenPath.FinProb.OrderedCoupling (c₀ e off₀) (c₁ e off₁))
    (hbit₀ : ∀ e off b, 0 < (c₀ e off).mass b)
    (hbit₁ : ∀ e off b, 0 < (c₁ e off).mass b)
    (ρ : OpenPath.FinProb E) (hρ : ∀ e, 0 < ρ.mass e)
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    OpenPath.FinProb.StochLe π₀ π₁ := by
  let K₀ := Glauber.mixture ρ (Glauber.edgeUpdate c₀)
  let K₁ := Glauber.mixture ρ (Glauber.edgeUpdate c₁)
  have ht₀ := mixture_tendsto π₀ π₀ c₀ hc₀ hbit₀ ρ hρ schedule hschedule
  have ht₁ := mixture_tendsto π₀ π₁ c₁ hc₁ hbit₁ ρ hρ schedule hschedule
  apply OpenPath.FinProb.stochLe_of_tendsto (l := Filter.atTop)
    (μn := fun n => π₀.bind (Glauber.iterate K₀ n))
    (νn := fun n => π₀.bind (Glauber.iterate K₁ n)) (μ := π₀) (ν := π₁)
  · intro n
    rw [← GlauberCoupling.iterateLaw_eq_bind_iterate π₀ K₀ n,
      ← GlauberCoupling.iterateLaw_eq_bind_iterate π₀ K₁ n]
    exact GlauberCoupling.FinProb.stochLe_iterateLaw π₀ K₀ K₁
      (GlauberCoupling.pairJump ρ c₀ c₁ s) n
  · exact ht₀
  · exact ht₁

/-- The lower classical comparison `Bernoulli(min(p,p')) ≤ FK`, in the
interior parameter range where both chains have full support. -/
theorem fk_stochLe_min_interior (G : LabelledMultigraph) [Nonempty G.Edge]
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (boolProduct (fun _ : G.Edge => fkLo q p) (fun _ => fkLo_mem_Icc hq hp1.le))
      (Glauber.ofPMF (G.fkPMF hq hp1.le ξ)) := by
  let cL : Glauber.EdgeConditionals Bool G.Edge :=
    fun e _ => boolLaw (fkLo q p) (fkLo_mem_Icc hq hp1.le)
  apply stochLe_of_ordered_conditionals
    (boolProduct (fun _ : G.Edge => fkLo q p) (fun _ => fkLo_mem_Icc hq hp1.le))
    (Glauber.ofPMF (G.fkPMF hq hp1.le ξ)) cL (fkConditionals G hq hp1.le ξ)
    (ρ := uniformClock G.Edge) (schedule := Finset.univ.toList)
  · intro e
    exact boolProduct_hasEdgeConditional (fun _ : G.Edge => fkLo q p)
      (fun _ => fkLo_mem_Icc hq hp1.le) e
  · intro e
    exact fk_hasEdgeConditional G hq hp1.le ξ e
  · intro e off₀ off₁
    exact boolOrderedCoupling (fkLo q p) (fkRate G q p ξ e off₁)
      (fkLo_mem_Icc hq hp1.le).1 (fkRate_ge_min G ξ e off₁)
      (fkRate_mem_Icc G hq hp1.le ξ e off₁).2
  · intro e off b
    exact boolLaw_pos (fkLo q p) (fkLo_pos hq hp0 hp1) (fkLo_lt_one hp1) b
  · intro e off b
    exact boolLaw_pos (fkRate G q p ξ e off) (fkRate_pos_interior G hq hp0 hp1 ξ e off)
      (fkRate_lt_one_interior G hq hp1 ξ e off) b
  · exact uniformClock_pos
  · intro e
    exact Finset.mem_toList.mpr (Finset.mem_univ e)

/-- The upper classical comparison `FK ≤ Bernoulli(max(p,p'))`, with the same
interior full-support hypothesis. -/
theorem fk_stochLe_max_interior (G : LabelledMultigraph) [Nonempty G.Edge]
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (Glauber.ofPMF (G.fkPMF hq hp1.le ξ))
      (boolProduct (fun _ : G.Edge => fkHi q p) (fun _ => fkHi_mem_Icc hq hp1.le)) := by
  let cH : Glauber.EdgeConditionals Bool G.Edge :=
    fun e _ => boolLaw (fkHi q p) (fkHi_mem_Icc hq hp1.le)
  apply stochLe_of_ordered_conditionals
    (Glauber.ofPMF (G.fkPMF hq hp1.le ξ))
    (boolProduct (fun _ : G.Edge => fkHi q p) (fun _ => fkHi_mem_Icc hq hp1.le))
    (fkConditionals G hq hp1.le ξ) cH
    (ρ := uniformClock G.Edge) (schedule := Finset.univ.toList)
  · intro e
    exact fk_hasEdgeConditional G hq hp1.le ξ e
  · intro e
    exact boolProduct_hasEdgeConditional (fun _ : G.Edge => fkHi q p)
      (fun _ => fkHi_mem_Icc hq hp1.le) e
  · intro e off₀ off₁
    exact boolOrderedCoupling (fkRate G q p ξ e off₀) (fkHi q p)
      (fkRate_mem_Icc G hq hp1.le ξ e off₀).1 (fkRate_le_max G ξ e off₀)
      (fkHi_mem_Icc hq hp1.le).2
  · intro e off b
    exact boolLaw_pos (fkRate G q p ξ e off) (fkRate_pos_interior G hq hp0 hp1 ξ e off)
      (fkRate_lt_one_interior G hq hp1 ξ e off) b
  · intro e off b
    exact boolLaw_pos (fkHi q p) (fkHi_pos hp0) (fkHi_lt_one hq hp1) b
  · exact uniformClock_pos
  · intro e
    exact Finset.mem_toList.mpr (Finset.mem_univ e)

lemma ofPMF_pure {α : Type*} [Fintype α] (a : α) :
    Glauber.ofPMF (PMF.pure a) = Glauber.FinProb.dirac a := by
  apply OpenPath.FinProb.ext
  intro b
  by_cases h : b = a <;> simp [Glauber.ofPMF_mass, Glauber.FinProb.dirac, h]

lemma boolProduct_eq_dirac_of_zero (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ e, r e = 0) :
    boolProduct r hr = Glauber.FinProb.dirac (fun _ => false) := by
  apply OpenPath.FinProb.ext
  intro ω
  by_cases hω : ω = fun _ => false
  · subst ω
    simp [boolProduct, OpenPath.FinProb.pi_mass, Glauber.FinProb.dirac, boolLaw, hzero]
  · have hex : ∃ e, ω e = true := by
      by_contra h
      apply hω
      funext e
      cases he : ω e <;> simp_all
    obtain ⟨e, he⟩ := hex
    simp only [boolProduct, OpenPath.FinProb.pi_mass, Glauber.FinProb.dirac, hω,
      ↓reduceIte]
    apply (Finset.prod_eq_zero_iff).mpr
    exact ⟨e, Finset.mem_univ e, by simp [boolLaw, hzero e, he]⟩

lemma boolProduct_eq_dirac_of_one (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ e, r e = 1) :
    boolProduct r hr = Glauber.FinProb.dirac (fun _ => true) := by
  apply OpenPath.FinProb.ext
  intro ω
  by_cases hω : ω = fun _ => true
  · subst ω
    simp [boolProduct, OpenPath.FinProb.pi_mass, Glauber.FinProb.dirac, boolLaw, hone]
  · have hex : ∃ e, ω e = false := by
      by_contra h
      apply hω
      funext e
      cases he : ω e <;> simp_all
    obtain ⟨e, he⟩ := hex
    simp only [boolProduct, OpenPath.FinProb.pi_mass, Glauber.FinProb.dirac, hω,
      ↓reduceIte]
    apply (Finset.prod_eq_zero_iff).mpr
    exact ⟨e, Finset.mem_univ e, by simp [boolLaw, hone e, he]⟩

lemma fkLo_zero (q : NNReal) : fkLo q 0 = 0 := by simp [fkLo, FK.prime]
lemma fkHi_zero (q : NNReal) : fkHi q 0 = 0 := by simp [fkHi, FK.prime]
lemma fkLo_one (q : NNReal) : fkLo q 1 = 1 := by simp [fkLo, FK.prime]
lemma fkHi_one (q : NNReal) : fkHi q 1 = 1 := by simp [fkHi, FK.prime]

/-- Full lower classical comparison, including both parameter endpoints. -/
theorem fk_stochLe_min (G : LabelledMultigraph) [Nonempty G.Edge]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (boolProduct (fun _ : G.Edge => fkLo q p) (fun _ => fkLo_mem_Icc hq hp))
      (Glauber.ofPMF (G.fkPMF hq hp ξ)) := by
  by_cases hp0 : p = 0
  · subst p
    have hprod := boolProduct_eq_dirac_of_zero
      (fun _ : G.Edge => fkLo q 0) (fun _ => fkLo_mem_Icc hq bot_le) (fun _ => fkLo_zero q)
    have hfk : Glauber.ofPMF (G.fkPMF hq bot_le ξ) = Glauber.FinProb.dirac G.allClosed := by
      rw [G.fkPMF_zero hq ξ, ofPMF_pure]
    rw [hprod, hfk]
    exact OpenPath.FinProb.stochLe_refl _
  · have hp0pos : 0 < p := pos_iff_ne_zero.mpr hp0
    by_cases hp1 : p = 1
    · subst p
      have hprod := boolProduct_eq_dirac_of_one
        (fun _ : G.Edge => fkLo q 1) (fun _ => fkLo_mem_Icc hq le_rfl) (fun _ => fkLo_one q)
      have hfk : Glauber.ofPMF (G.fkPMF hq le_rfl ξ) = Glauber.FinProb.dirac G.allOpen := by
        rw [G.fkPMF_one hq ξ, ofPMF_pure]
      rw [hprod, hfk]
      exact OpenPath.FinProb.stochLe_refl _
    · exact fk_stochLe_min_interior G hq hp0pos (lt_of_le_of_ne hp hp1) ξ

/-- Full upper classical comparison, including both parameter endpoints. -/
theorem fk_stochLe_max (G : LabelledMultigraph) [Nonempty G.Edge]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (Glauber.ofPMF (G.fkPMF hq hp ξ))
      (boolProduct (fun _ : G.Edge => fkHi q p) (fun _ => fkHi_mem_Icc hq hp)) := by
  by_cases hp0 : p = 0
  · subst p
    have hprod := boolProduct_eq_dirac_of_zero
      (fun _ : G.Edge => fkHi q 0) (fun _ => fkHi_mem_Icc hq bot_le) (fun _ => fkHi_zero q)
    have hfk : Glauber.ofPMF (G.fkPMF hq bot_le ξ) = Glauber.FinProb.dirac G.allClosed := by
      rw [G.fkPMF_zero hq ξ, ofPMF_pure]
    rw [hfk, hprod]
    exact OpenPath.FinProb.stochLe_refl _
  · have hp0pos : 0 < p := pos_iff_ne_zero.mpr hp0
    by_cases hp1 : p = 1
    · subst p
      have hprod := boolProduct_eq_dirac_of_one
        (fun _ : G.Edge => fkHi q 1) (fun _ => fkHi_mem_Icc hq le_rfl) (fun _ => fkHi_one q)
      have hfk : Glauber.ofPMF (G.fkPMF hq le_rfl ξ) = Glauber.FinProb.dirac G.allOpen := by
        rw [G.fkPMF_one hq ξ, ofPMF_pure]
      rw [hfk, hprod]
      exact OpenPath.FinProb.stochLe_refl _
    · exact fk_stochLe_max_interior G hq hp0pos (lt_of_le_of_ne hp hp1) ξ

lemma finProb_eq_of_subsingleton {α : Type*} [Fintype α] [Subsingleton α]
    (μ ν : OpenPath.FinProb α) : μ = ν := by
  apply OpenPath.FinProb.ext
  intro a
  have hμ : μ.mass a = 1 := by
    have hs : ∑ b, μ.mass b = μ.mass a := by
      apply Finset.sum_eq_single a
      · intro b _ hb
        exact (hb (Subsingleton.elim b a)).elim
      · simp
    exact hs.symm.trans μ.sum_mass
  have hν : ν.mass a = 1 := by
    have hs : ∑ b, ν.mass b = ν.mass a := by
      apply Finset.sum_eq_single a
      · intro b _ hb
        exact (hb (Subsingleton.elim b a)).elim
      · simp
    exact hs.symm.trans ν.sum_mass
  rw [hμ, hν]

/-- Equation (3) for a graph with no edges: there is exactly one probability
law on the one-point configuration space. -/
theorem fk_stochLe_min_of_isEmpty (G : LabelledMultigraph) [IsEmpty G.Edge]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (boolProduct (fun _ : G.Edge => fkLo q p) (fun _ => fkLo_mem_Icc hq hp))
      (Glauber.ofPMF (G.fkPMF hq hp ξ)) := by
  let _ : Subsingleton G.Configuration :=
    ⟨fun ω η => funext fun e => (IsEmpty.false e).elim⟩
  rw [finProb_eq_of_subsingleton
    (boolProduct (fun _ : G.Edge => fkLo q p) (fun _ => fkLo_mem_Icc hq hp))
    (Glauber.ofPMF (G.fkPMF hq hp ξ))]
  exact OpenPath.FinProb.stochLe_refl _

/-- The empty-edge case of the upper comparison. -/
theorem fk_stochLe_max_of_isEmpty (G : LabelledMultigraph) [IsEmpty G.Edge]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (Glauber.ofPMF (G.fkPMF hq hp ξ))
      (boolProduct (fun _ : G.Edge => fkHi q p) (fun _ => fkHi_mem_Icc hq hp)) := by
  let _ : Subsingleton G.Configuration :=
    ⟨fun ω η => funext fun e => (IsEmpty.false e).elim⟩
  rw [finProb_eq_of_subsingleton
    (Glauber.ofPMF (G.fkPMF hq hp ξ))
    (boolProduct (fun _ : G.Edge => fkHi q p) (fun _ => fkHi_mem_Icc hq hp))]
  exact OpenPath.FinProb.stochLe_refl _

/-- Full equation (3), lower direction, on every finite labelled multigraph. -/
theorem fk_stochLe_min_all (G : LabelledMultigraph)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (boolProduct (fun _ : G.Edge => fkLo q p) (fun _ => fkLo_mem_Icc hq hp))
      (Glauber.ofPMF (G.fkPMF hq hp ξ)) := by
  cases isEmpty_or_nonempty G.Edge with
  | inl hE =>
      let _ := hE
      exact fk_stochLe_min_of_isEmpty G hq hp ξ
  | inr hE =>
      let _ := hE
      exact fk_stochLe_min G hq hp ξ

/-- Full equation (3), upper direction, on every finite labelled multigraph. -/
theorem fk_stochLe_max_all (G : LabelledMultigraph)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    OpenPath.FinProb.StochLe
      (Glauber.ofPMF (G.fkPMF hq hp ξ))
      (boolProduct (fun _ : G.Edge => fkHi q p) (fun _ => fkHi_mem_Icc hq hp)) := by
  cases isEmpty_or_nonempty G.Edge with
  | inl hE =>
      let _ := hE
      exact fk_stochLe_max_of_isEmpty G hq hp ξ
  | inr hE =>
      let _ := hE
      exact fk_stochLe_max G hq hp ξ

end
end FK.Finite.Comparison
