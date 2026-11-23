import FK.CanonicalDisintegration
import FK.FiniteComparison

/-!
# Conditional open rates are mixed through arbitrary off-edge fibers

A singleton heat-bath bound at rate `r` implies the same bound after
conditioning on any union of off-edge fibers.  This is the elementary step
needed for canonical prefix conditionals; global stochastic order is neither
used nor claimed to be preserved by conditioning.
-/

namespace FK.Exploration.Sequential

open scoped ENNReal BigOperators Classical
open FK.Finite.Comparison

/-- Sum a real-valued quantity over a predicate-selected collection of
points of a finite type. -/
noncomputable def selectedSum {α : Type*} [Fintype α] (S : Set α) (f : α → ℝ) : ℝ :=
  ∑ a, if a ∈ S then f a else 0

/-- Exact off-fiber conditional openness, averaged over an arbitrary event in
the off-edge coordinates. -/
theorem selected_openMass_le {E : Type*} [Fintype E] [DecidableEq E]
    (μ : OpenPath.FinProb (E → Bool)) (c : Glauber.EdgeConditionals Bool E)
    (e : E) (hc : Glauber.HasEdgeConditional μ c e)
    (r : ℝ) (hr : ∀ off, (c e off).mass true ≤ r) (S : Set (Glauber.OffConfig Bool E e)) :
    selectedSum S (fun off => μ.mass ((Glauber.configSplit Bool e).symm (off, true))) ≤
      r * selectedSum S (Glauber.outsideMassConj (Glauber.configSplit Bool e) μ) := by
  calc
    selectedSum S (fun off => μ.mass ((Glauber.configSplit Bool e).symm (off, true))) =
        selectedSum S (fun off =>
          Glauber.outsideMassConj (Glauber.configSplit Bool e) μ off *
            (c e off).mass true) := by
      apply Finset.sum_congr rfl
      intro off _
      by_cases h : off ∈ S <;> simp [selectedSum, h, hc off true]
    _ ≤ selectedSum S (fun off =>
          Glauber.outsideMassConj (Glauber.configSplit Bool e) μ off * r) := by
      unfold selectedSum
      apply Finset.sum_le_sum
      intro off _
      by_cases h : off ∈ S
      · simp only [h, if_true]
        apply mul_le_mul_of_nonneg_left (hr off)
        apply Finset.sum_nonneg
        intro b _
        exact μ.mass_nonneg _
      · simp [h]
    _ = r * selectedSum S (Glauber.outsideMassConj (Glauber.configSplit Bool e) μ) := by
      unfold selectedSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro off _
      by_cases h : off ∈ S <;> simp [h, mul_comm]

/-- The mass of an off-edge fiber is the sum of its open and closed masses. -/
lemma selected_outsideMass_eq_open_add_closed {E : Type*} [Fintype E] [DecidableEq E]
    (μ : OpenPath.FinProb (E → Bool)) (e : E) (S : Set (Glauber.OffConfig Bool E e)) :
    selectedSum S (Glauber.outsideMassConj (Glauber.configSplit Bool e) μ) =
      selectedSum S (fun off => μ.mass ((Glauber.configSplit Bool e).symm (off, true))) +
      selectedSum S (fun off => μ.mass ((Glauber.configSplit Bool e).symm (off, false))) := by
  unfold selectedSum Glauber.outsideMassConj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro off _
  by_cases h : off ∈ S <;> simp [h, Fintype.sum_bool]

/-- Prefixes shorter than the total configuration length do not depend on an
update of the coordinate immediately after them. -/
lemma prefix_ofFn_update_iff {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (ω : Fin n → Bool) (x : List Bool)
    (hx : x.length < n) (b : Bool) :
    x <+: List.ofFn (Function.update ω ⟨x.length, hx⟩ b) ↔
      x <+: List.ofFn ω := by
  rw [List.prefix_iff_getElem, List.prefix_iff_getElem]
  constructor <;> rintro ⟨hlen, h⟩ <;> refine ⟨by simpa using hlen, ?_⟩
  · intro i hi
    have hget := h i hi
    have hine : (⟨i, by omega⟩ : Fin n) ≠ ⟨x.length, hx⟩ := by
      intro heq
      have : i = x.length := congrArg Fin.val heq
      omega
    simpa only [List.getElem_ofFn, Function.update_of_ne hine] using hget
  · intro i hi
    have hget := h i hi
    have hine : (⟨i, by omega⟩ : Fin n) ≠ ⟨x.length, hx⟩ := by
      intro heq
      have : i = x.length := congrArg Fin.val heq
      omega
    simpa only [List.getElem_ofFn, Function.update_of_ne hine] using hget

/-- The off-fiber consisting of configurations with a prescribed positive
length prefix. -/
def offPrefix {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (x : List Bool) (hx : x.length < n) :
    Set (Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩) :=
  {off | x <+: List.ofFn (fullOff ⟨x.length, hx⟩ off)}

lemma mem_offPrefix_iff_open {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (x : List Bool) (hx : x.length < n)
    (off : Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩) :
    x <+: List.ofFn ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)) ↔
      off ∈ offPrefix x hx := by
  have h := prefix_ofFn_update_iff (fullOff ⟨x.length, hx⟩ off) x hx true
  change x <+: List.ofFn ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)) ↔
    x <+: List.ofFn (fullOff ⟨x.length, hx⟩ off)
  simpa only [recombine_off] using h

lemma mem_offPrefix_iff_closed {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (x : List Bool) (hx : x.length < n)
    (off : Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩) :
    x <+: List.ofFn ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, false)) ↔
      off ∈ offPrefix x hx := by
  have h := prefix_ofFn_update_iff (fullOff ⟨x.length, hx⟩ off) x hx false
  change x <+: List.ofFn ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, false)) ↔
    x <+: List.ofFn (fullOff ⟨x.length, hx⟩ off)
  simpa only [recombine_off] using h

/-- Open extension at the next coordinate is exactly the conjunction of the
current off-prefix event and the open value in that off-fiber. -/
lemma mem_offPrefix_iff_open_extended {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (x : List Bool) (hx : x.length < n)
    (off : Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩) :
    x ++ [true] <+: List.ofFn
      ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)) ↔
      off ∈ offPrefix x hx := by
  let ω : Fin n → Bool := (Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)
  rw [prefix_append_bit_iff ω x true hx]
  have hpre : x <+: List.ofFn ω ↔ off ∈ offPrefix x hx := mem_offPrefix_iff_open x hx off
  have hbit : true = ω ⟨x.length, hx⟩ := by
    dsimp [ω]
    rw [recombine_off]
    simp
  simp [hpre, hbit]

lemma mem_offPrefix_iff_extended {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (x : List Bool) (hx : x.length < n)
    (off : Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩) (b : Bool) :
    x ++ [b] <+: List.ofFn
      ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b)) ↔
      off ∈ offPrefix x hx := by
  let ω : Fin n → Bool := (Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b)
  rw [prefix_append_bit_iff ω x b hx]
  have hpre : x <+: List.ofFn ω ↔ off ∈ offPrefix x hx := by
    cases b with
    | false => exact mem_offPrefix_iff_closed x hx off
    | true => exact mem_offPrefix_iff_open x hx off
  have hbit : b = ω ⟨x.length, hx⟩ := by
    dsimp [ω]
    rw [recombine_off]
    simp
  simp [hpre, hbit]

/-- Reindex a real prefix-cylinder mass into pairs consisting of an off-edge
restriction and the next bit. -/
lemma cylMass_toReal_decompose {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (μ : PMF (Fin n → Bool))
    (x : List Bool) (hx : x.length < n) (y : List Bool) :
    (cylMass μ y).toReal =
      ∑ off : Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩,
        ∑ b : Bool, if y <+: List.ofFn
          ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b)) then
            (μ ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b))).toReal else 0 := by
  rw [cylMass, tsum_fintype]
  have htop : ∀ ω ∈ Finset.univ,
      (prefixCylinder y).indicator (⇑μ) ω ≠ ⊤ := by
    intro ω _
    by_cases h : ω ∈ prefixCylinder y
    · simp [Set.indicator_of_mem h, μ.apply_ne_top]
    · simp [Set.indicator_of_notMem h]
  rw [ENNReal.toReal_sum htop]
  calc
    (∑ ω, ((prefixCylinder y).indicator (⇑μ) ω).toReal) =
        ∑ z : Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩ × Bool,
          (((prefixCylinder y).indicator (⇑μ))
            ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm z)).toReal := by
      simpa only [(Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm_apply_apply] using
        (Equiv.sum_comp (Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n))
          (fun z => (((prefixCylinder y).indicator (⇑μ))
            ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm z)).toReal))
    _ = ∑ off : Glauber.OffConfig Bool (Fin n) ⟨x.length, hx⟩,
        ∑ b : Bool, (((prefixCylinder y).indicator (⇑μ))
            ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b))).toReal := by
      rw [Fintype.sum_prod_type]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro off _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : (Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b) ∈
          prefixCylinder y
      · have hp : y <+: List.ofFn
          ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b)) := h
        rw [Set.indicator_of_mem h, if_pos hp]
      · have hp : ¬ y <+: List.ofFn
          ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, b)) := h
        rw [Set.indicator_of_notMem h, if_neg hp]
        rfl

/-- The denominator of a canonical next-prefix conditional is precisely the
selected outside mass on the corresponding off-fibers. -/
theorem cylMass_toReal_eq_selected_outside {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (μ : PMF (Fin n → Bool))
    (x : List Bool) (hx : x.length < n) :
    (cylMass μ x).toReal =
      selectedSum (offPrefix x hx) (Glauber.outsideMassConj
        (Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)) (Glauber.ofPMF μ)) := by
  rw [cylMass_toReal_decompose μ x hx x]
  unfold selectedSum Glauber.outsideMassConj
  apply Finset.sum_congr rfl
  intro off _
  simp_rw [Fintype.sum_bool]
  by_cases hoff : off ∈ offPrefix x hx
  · have hopen : x <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)) :=
      (mem_offPrefix_iff_open x hx off).mpr hoff
    have hclosed : x <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, false)) :=
      (mem_offPrefix_iff_closed x hx off).mpr hoff
    simp [hoff, hopen, hclosed, Glauber.ofPMF_mass]
  · have hopen : ¬ x <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)) := by
      intro h
      exact hoff ((mem_offPrefix_iff_open x hx off).mp h)
    have hclosed : ¬ x <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, false)) := by
      intro h
      exact hoff ((mem_offPrefix_iff_closed x hx off).mp h)
    simp [hoff, hopen, hclosed, Glauber.ofPMF_mass]

/-- The numerator at the open next bit is precisely the selected open mass on
the same off-fibers. -/
theorem cylMass_open_toReal_eq_selected_open {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (μ : PMF (Fin n → Bool))
    (x : List Bool) (hx : x.length < n) :
    (cylMass μ (x ++ [true])).toReal =
      selectedSum (offPrefix x hx) (fun off =>
        (Glauber.ofPMF μ).mass
          ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true))) := by
  rw [cylMass_toReal_decompose μ x hx (x ++ [true])]
  unfold selectedSum
  apply Finset.sum_congr rfl
  intro off _
  rw [Fintype.sum_bool]
  by_cases hoff : off ∈ offPrefix x hx
  · have hopen : x ++ [true] <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)) :=
      (mem_offPrefix_iff_extended x hx off true).mpr hoff
    have hclosed : ¬ x ++ [true] <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, false)) := by
      intro h
      have hb := ((prefix_append_bit_iff _ x true hx).mp h).2
      rw [recombine_off] at hb
      simp at hb
    simp [hoff, hopen, hclosed, Glauber.ofPMF_mass]
  · have hopen : ¬ x ++ [true] <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, true)) := by
      intro h
      exact hoff ((mem_offPrefix_iff_extended x hx off true).mp h)
    have hclosed : ¬ x ++ [true] <+: List.ofFn
        ((Glauber.configSplit Bool (⟨x.length, hx⟩ : Fin n)).symm (off, false)) := by
      intro h
      have hb := ((prefix_append_bit_iff _ x true hx).mp h).2
      rw [recombine_off] at hb
      simp at hb
    simp [hoff, hopen, hclosed, Glauber.ofPMF_mass]

/-- Exact constant-rate factorization on every selected off-edge fiber. -/
theorem selected_openMass_eq {E : Type*} [Fintype E] [DecidableEq E]
    (μ : OpenPath.FinProb (E → Bool)) (c : Glauber.EdgeConditionals Bool E)
    (e : E) (hc : Glauber.HasEdgeConditional μ c e)
    (r : ℝ) (hr : ∀ off, (c e off).mass true = r)
    (S : Set (Glauber.OffConfig Bool E e)) :
    selectedSum S (fun off => μ.mass ((Glauber.configSplit Bool e).symm (off, true))) =
      r * selectedSum S (Glauber.outsideMassConj (Glauber.configSplit Bool e) μ) := by
  calc
    selectedSum S (fun off => μ.mass ((Glauber.configSplit Bool e).symm (off, true))) =
        selectedSum S (fun off =>
          Glauber.outsideMassConj (Glauber.configSplit Bool e) μ off *
            (c e off).mass true) := by
      apply Finset.sum_congr rfl
      intro off _
      by_cases h : off ∈ S <;> simp [selectedSum, h, hc off true]
    _ = r * selectedSum S (Glauber.outsideMassConj (Glauber.configSplit Bool e) μ) := by
      unfold selectedSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro off _
      by_cases h : off ∈ S <;> simp [h, hr off, mul_comm]

/-- The next-open mass of any canonical prefix conditional obeys every uniform
upper bound obeyed by the singleton heat-bath conditionals. -/
theorem nextBit_true_toReal_le {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (hx : x.length < n)
    (c : Glauber.EdgeConditionals Bool (Fin n))
    (hc : Glauber.HasEdgeConditional (Glauber.ofPMF μ) c ⟨x.length, hx⟩)
    (r : ℝ) (hr : ∀ off, (c ⟨x.length, hx⟩ off).mass true ≤ r) :
    (nextBit μ hμ x hx true).toReal ≤ r := by
  have hmass := selected_openMass_le (Glauber.ofPMF μ) c ⟨x.length, hx⟩ hc r hr
    (offPrefix x hx)
  rw [← cylMass_open_toReal_eq_selected_open μ x hx,
    ← cylMass_toReal_eq_selected_outside μ x hx] at hmass
  have hpos : 0 < (cylMass μ x).toReal := ENNReal.toReal_pos
    (ne_of_gt (cylMass_pos_of_positive μ hμ x hx.le)) (cylMass_ne_top μ x)
  rw [nextBit_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ← div_eq_mul_inv]
  exact (div_le_iff₀ hpos).mpr hmass

/-- Under exact constant singleton open rates, the canonical next-prefix open
mass is exactly that constant rate. -/
theorem nextBit_true_toReal_eq {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (hx : x.length < n)
    (c : Glauber.EdgeConditionals Bool (Fin n))
    (hc : Glauber.HasEdgeConditional (Glauber.ofPMF μ) c ⟨x.length, hx⟩)
    (r : ℝ) (hr : ∀ off, (c ⟨x.length, hx⟩ off).mass true = r) :
    (nextBit μ hμ x hx true).toReal = r := by
  have hmass := selected_openMass_eq (Glauber.ofPMF μ) c ⟨x.length, hx⟩ hc r hr
    (offPrefix x hx)
  rw [← cylMass_open_toReal_eq_selected_open μ x hx,
    ← cylMass_toReal_eq_selected_outside μ x hx] at hmass
  have hpos : 0 < (cylMass μ x).toReal := ENNReal.toReal_pos
    (ne_of_gt (cylMass_pos_of_positive μ hμ x hx.le)) (cylMass_ne_top μ x)
  rw [nextBit_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ← div_eq_mul_inv]
  exact (div_eq_iff hpos.ne').mpr hmass

/-- The open mass of a finite Bool law as a nonnegative real. -/
noncomputable def openRate (p : PMF Bool) : NNReal := (p true).toNNReal

/-- A Bool PMF is determined by its open mass. -/
lemma eq_of_true_toReal_eq (p q : PMF Bool)
    (h : (p true).toReal = (q true).toReal) : p = q := by
  have ht : p true = q true := by
    apply le_antisymm
    · exact (ENNReal.toReal_le_toReal (p.apply_ne_top true) (q.apply_ne_top true)).mp
        (le_of_eq h)
    · exact (ENNReal.toReal_le_toReal (q.apply_ne_top true) (p.apply_ne_top true)).mp
        (le_of_eq h.symm)
  apply PMF.ext
  intro b
  cases b with
  | false =>
      have hp := p.tsum_coe
      have hq := q.tsum_coe
      rw [tsum_fintype, Fintype.sum_bool] at hp hq
      have hp' : p false = 1 - p true :=
        ENNReal.sub_eq_of_eq_add (p.apply_ne_top true) (by rw [add_comm, hp]) |>.symm
      have hq' : q false = 1 - q true :=
        ENNReal.sub_eq_of_eq_add (q.apply_ne_top true) (by rw [add_comm, hq]) |>.symm
      rw [hp', hq', ht]
  | true => exact ht

/-- The common-uniform ordered coupling of two Bool laws from an open-mass
inequality, avoiding any finite-state Strassen theorem. -/
noncomputable def boolOrderedCouplingOfLe (p : PMF Bool)
    (r : NNReal) (hr : r ≤ 1) (hpr : (p true).toReal ≤ (r : ℝ)) :
    PMF.OrderedCoupling p (FKModel.bernoulliPMF r hr) := by
  have hp1 : openRate p ≤ 1 := by
    rw [← ENNReal.coe_le_coe]
    exact (ENNReal.coe_toNNReal (p.apply_ne_top true)).trans_le (by
      have h := p.tsum_coe
      rw [tsum_fintype, Fintype.sum_bool] at h
      exact (le_add_of_nonneg_right (bot_le : 0 ≤ p false)).trans_eq h)
  have hpr' : openRate p ≤ r := by
    rw [← ENNReal.coe_le_coe]
    exact (ENNReal.coe_toNNReal (p.apply_ne_top true)).trans_le
      ((ENNReal.toReal_le_toReal (p.apply_ne_top true) ENNReal.coe_ne_top).mp (by simpa using hpr))
  have heq : FKModel.bernoulliPMF (openRate p) hp1 = p := by
    apply eq_of_true_toReal_eq
    rw [FKModel.bernoulliPMF_apply]
    change (p true).toReal = (p true).toReal
    rfl
  let c := FKModel.boolCoupling (openRate p) r hp1 hr hpr'
  exact {
    dist := c
    map_fst := (FKModel.map_fst_boolCoupling (openRate p) r hp1 hr hpr').trans heq
    map_snd := FKModel.map_snd_boolCoupling (openRate p) r hp1 hr hpr'
    ordered := by
      intro z hz
      have hm : c z ≠ 0 := (PMF.mem_support_iff c z).mp hz
      rcases z with ⟨a, b⟩
      cases a <;> cases b
      · exact le_rfl
      · decide
      · exact (hm (FKModel.boolCoupling_true_false (openRate p) r hp1 hr hpr')).elim
      · exact le_rfl
  }

end FK.Exploration.Sequential
