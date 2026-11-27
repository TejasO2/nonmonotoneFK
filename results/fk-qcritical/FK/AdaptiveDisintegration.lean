import FK.ConditionalRate

/-!
# Adaptive disintegration of finite configuration laws

A partial configuration records an optional Boolean value on every edge.  The
next edge may depend on the revealed upper partial configuration.  Sampling a
new lower bit from the exact finite conditional law and then iterating still
reconstructs the original law.  This is the probabilistic content of inward
exploration, without fixing an edge enumeration in advance.
-/

namespace FK.Adaptive

open scoped ENNReal BigOperators Classical
open Set

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A finite partial Boolean configuration. -/
abbrev Assignment (E : Type*) := E → Option Bool

/-- Full configurations compatible with a partial assignment. -/
def Fiber (h : Assignment E) : Set (E → Bool) :=
  {ω | ∀ e b, h e = some b → ω e = b}

/-- Reveal one further coordinate. -/
def reveal (h : Assignment E) (e : E) (b : Bool) : Assignment E :=
  Function.update h e (some b)

/-- A canonical full extension of a partial assignment. -/
def decodeOption (h : Assignment E) : E → Bool := fun e => (h e).getD false

lemma decodeOption_mem_fiber (h : Assignment E) : decodeOption h ∈ Fiber h := by
  intro e b hb
  simp [decodeOption, hb]

lemma fiber_support_of_positive (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (h : Assignment E) :
    ∃ ω ∈ Fiber h, ω ∈ μ.support := by
  exact ⟨decodeOption h, decodeOption_mem_fiber h,
    (PMF.mem_support_iff _ _).2 (hμ _)⟩

/-- The exact law conditioned on a revealed partial configuration. -/
noncomputable def cond (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (h : Assignment E) : PMF (E → Bool) :=
  μ.filter (Fiber h) (fiber_support_of_positive μ hμ h)

/-- Unnormalized mass of a partial-assignment fibre. -/
noncomputable def mass (μ : PMF (E → Bool)) (h : Assignment E) : ℝ≥0∞ :=
  ∑' ω, (Fiber h).indicator (⇑μ) ω

lemma mem_fiber_reveal_iff {h : Assignment E} {e : E} (he : h e = none)
    {b : Bool} {ω : E → Bool} :
    ω ∈ Fiber (reveal h e b) ↔ ω ∈ Fiber h ∧ ω e = b := by
  constructor
  · intro hω
    have hval : ω e = b := by
      apply hω e b
      simp [reveal]
    refine ⟨?_, hval⟩
    intro a c ha
    apply hω a c
    by_cases hae : a = e
    · subst a
      rw [he] at ha
      contradiction
    · simp [reveal, Function.update_of_ne hae, ha]
  · rintro ⟨hω, hval⟩ a c ha
    by_cases hae : a = e
    · subst a
      have hbc : b = c := by simpa [reveal] using ha
      exact hval.trans hbc
    · apply hω a c
      simpa [reveal, Function.update_of_ne hae] using ha

lemma mass_ne_top (μ : PMF (E → Bool)) (h : Assignment E) : mass μ h ≠ ∞ := by
  have hle : mass μ h ≤ ∑' ω, μ ω := by
    apply ENNReal.tsum_le_tsum
    intro ω
    by_cases hω : ω ∈ Fiber h <;> simp [Set.indicator, hω]
  rw [μ.tsum_coe] at hle
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

lemma mass_pos_of_positive (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (h : Assignment E) : 0 < mass μ h := by
  rw [mass, tsum_fintype]
  have hterm : 0 < (Fiber h).indicator (⇑μ) (decodeOption h) := by
    simp [Set.indicator_of_mem (decodeOption_mem_fiber h), pos_iff_ne_zero, hμ]
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (fun ω _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ (decodeOption h)))

/-- The revealed conditional probability of one further coordinate. -/
noncomputable def bit (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (h : Assignment E) (e : E) : PMF Bool :=
  (cond μ hμ h).map (fun ω => ω e)

lemma cond_apply (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (h : Assignment E) (ω : E → Bool) :
    cond μ hμ h ω = (Fiber h).indicator (⇑μ) ω * (mass μ h)⁻¹ := by
  rw [cond, PMF.filter_apply]
  rfl

lemma bit_apply {h : Assignment E} {e : E} (he : h e = none)
    (μ : PMF (E → Bool)) (hμ : ∀ ω, μ ω ≠ 0) (b : Bool) :
    bit μ hμ h e b = mass μ (reveal h e b) * (mass μ h)⁻¹ := by
  unfold bit
  rw [PMF.map_apply]
  calc
    _ = ∑' ω : E → Bool,
        (Fiber (reveal h e b)).indicator (⇑μ) ω * (mass μ h)⁻¹ := by
      apply tsum_congr
      intro ω
      rw [cond_apply]
      by_cases hb : b = ω e
      · subst b
        by_cases hω : ω ∈ Fiber h
        · have hnew : ω ∈ Fiber (reveal h e (ω e)) :=
            (mem_fiber_reveal_iff he).2 ⟨hω, rfl⟩
          simp [Set.indicator_of_mem hω, Set.indicator_of_mem hnew]
        · have hnew : ω ∉ Fiber (reveal h e (ω e)) := by
            intro hn
            exact hω ((mem_fiber_reveal_iff he).1 hn).1
          simp [Set.indicator_of_notMem hω, Set.indicator_of_notMem hnew]
      · have hnew : ω ∉ Fiber (reveal h e b) := by
          intro hn
          exact hb ((mem_fiber_reveal_iff he).1 hn).2.symm
        simp [hb, Set.indicator_of_notMem hnew]
    _ = mass μ (reveal h e b) * (mass μ h)⁻¹ := by
      rw [ENNReal.tsum_mul_right]
      rfl

/-- Tower identity for arbitrary revealed coordinate order. -/
theorem bind_bit_cond {h : Assignment E} {e : E} (he : h e = none)
    (μ : PMF (E → Bool)) (hμ : ∀ ω, μ ω ≠ 0) :
    (bit μ hμ h e).bind (fun b => cond μ hμ (reveal h e b)) = cond μ hμ h := by
  apply PMF.ext
  intro ω
  rw [PMF.bind_apply, tsum_fintype]
  by_cases hω : ω ∈ Fiber h
  · have honly : ∀ b : Bool, ω ∈ Fiber (reveal h e b) ↔ b = ω e := by
      intro b
      rw [mem_fiber_reveal_iff he]
      exact and_iff_right hω |>.trans (by constructor <;> intro h; exact h.symm; exact h.symm)
    calc
      (∑ b, bit μ hμ h e b * cond μ hμ (reveal h e b) ω) =
          bit μ hμ h e (ω e) * cond μ hμ (reveal h e (ω e)) ω := by
        apply Finset.sum_eq_single (ω e)
        · intro b _ hb
          have hn : ω ∉ Fiber (reveal h e b) := by
            rw [honly]
            exact hb
          rw [cond_apply, Set.indicator_of_notMem hn]
          simp
        · intro hn
          simp at hn
      _ = mass μ (reveal h e (ω e)) * (mass μ h)⁻¹ *
          ((Fiber (reveal h e (ω e))).indicator (⇑μ) ω *
            (mass μ (reveal h e (ω e)))⁻¹) := by
        rw [bit_apply he, cond_apply]
      _ = μ ω * (mass μ h)⁻¹ := by
        have hn : ω ∈ Fiber (reveal h e (ω e)) := (honly (ω e)).2 rfl
        rw [Set.indicator_of_mem hn]
        have hm0 : mass μ (reveal h e (ω e)) ≠ 0 :=
          ne_of_gt (mass_pos_of_positive μ hμ _)
        have hmt : mass μ (reveal h e (ω e)) ≠ ∞ := mass_ne_top μ _
        calc
          _ = μ ω * (mass μ h)⁻¹ *
              (mass μ (reveal h e (ω e)) * (mass μ (reveal h e (ω e)))⁻¹) := by
            ac_rfl
          _ = _ := by rw [ENNReal.mul_inv_cancel hm0 hmt, mul_one]
      _ = cond μ hμ h ω := by rw [cond_apply, Set.indicator_of_mem hω]
  · have hr : cond μ hμ h ω = 0 := by
      rw [cond_apply, Set.indicator_of_notMem hω]
      simp
    rw [hr]
    apply Finset.sum_eq_zero
    intro b _
    have hn : ω ∉ Fiber (reveal h e b) := by
      intro hn
      exact hω ((mem_fiber_reveal_iff he).1 hn).1
    rw [cond_apply, Set.indicator_of_notMem hn]
    simp

/-- Coordinates which have not yet been revealed. -/
def unrevealed (h : Assignment E) : Finset E :=
  Finset.univ.filter (fun e => h e = none)

@[simp] lemma mem_unrevealed {h : Assignment E} {e : E} :
    e ∈ unrevealed h ↔ h e = none := by simp [unrevealed]

lemma unrevealed_reveal {h : Assignment E} {e : E} (he : h e = none) (b : Bool) :
    unrevealed (reveal h e b) = (unrevealed h).erase e := by
  ext a
  by_cases hae : a = e
  · subst a
    simp [reveal, he]
  · rw [mem_unrevealed]
    change Function.update h e (some b) a = none ↔ a ∈ (unrevealed h).erase e
    rw [Function.update_of_ne hae]
    simp [hae]

lemma card_unrevealed_reveal {h : Assignment E} {e : E} (he : h e = none)
    (b : Bool) : (unrevealed (reveal h e b)).card + 1 = (unrevealed h).card := by
  rw [unrevealed_reveal he]
  exact Finset.card_erase_add_one (mem_unrevealed.2 he)

lemma decodeOption_reveal (h : Assignment E) (e : E) (b : Bool) :
    decodeOption (reveal h e b) = Function.update (decodeOption h) e b := by
  funext a
  by_cases hae : a = e
  · subst a
    simp [decodeOption, reveal]
  · simp [decodeOption, reveal, Function.update_of_ne hae]

lemma decodeOption_reveal_le {h k : Assignment E} {e : E} {a b : Bool}
    (hle : decodeOption h ≤ decodeOption k) (hab : a ≤ b) :
    decodeOption (reveal h e a) ≤ decodeOption (reveal k e b) := by
  rw [decodeOption_reveal, decodeOption_reveal]
  intro x
  by_cases hx : x = e
  · subst x
    simpa using hab
  · simpa [Function.update_of_ne hx] using hle x

lemma eq_decodeOption_of_mem_fiber {h : Assignment E} {ω : E → Bool}
    (hh : unrevealed h = ∅) (hω : ω ∈ Fiber h) : ω = decodeOption h := by
  funext e
  cases he : h e with
  | none =>
      have he' : e ∈ unrevealed h := mem_unrevealed.2 he
      rw [hh] at he'
      exact (Finset.notMem_empty e he').elim
  | some b => exact (hω e b he).trans (by simp [decodeOption, he])

lemma cond_eq_pure_of_unrevealed_eq_empty (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) {h : Assignment E}
    (hh : unrevealed h = ∅) : cond μ hμ h = PMF.pure (decodeOption h) := by
  have hfib : Fiber h = {decodeOption h} := by
    ext ω
    constructor
    · intro hω
      have heq := eq_decodeOption_of_mem_fiber hh hω
      simpa [heq]
    · intro hω
      have heq : ω = decodeOption h := by simpa using hω
      subst ω
      exact decodeOption_mem_fiber h
  have hm : mass μ h = μ (decodeOption h) := by
    rw [mass, hfib]
    simp
  apply PMF.ext
  intro ω
  rw [cond_apply]
  by_cases hω : ω = decodeOption h
  · subst ω
    have hmem : decodeOption h ∈ Fiber h := decodeOption_mem_fiber h
    rw [PMF.pure_apply, if_pos rfl, Set.indicator_of_mem hmem, hm]
    exact ENNReal.mul_inv_cancel (hμ _) (μ.apply_ne_top _)
  · have hn : ω ∉ Fiber h := by rw [hfib]; simpa
    rw [PMF.pure_apply, if_neg hω, Set.indicator_of_notMem hn]
    simp

/-- An adaptive paired process on partial assignments. -/
noncomputable def run
    (step : Assignment E → Assignment E → E → PMF (Bool × Bool))
    (next : Assignment E → E) (h k : Assignment E) : ℕ → PMF (Assignment E × Assignment E)
  | 0 => PMF.pure (h, k)
  | n + 1 =>
      let e := next k
      (step h k e).bind (fun z =>
        run step next (reveal h e z.1) (reveal k e z.2) n)

lemma unrevealed_reveal_pair_eq {h k : Assignment E}
    (hhk : unrevealed h = unrevealed k) (e : E) (a b : Bool) :
    unrevealed (reveal h e a) = unrevealed (reveal k e b) := by
  ext x
  by_cases hx : x = e
  · subst x
    simp [reveal]
  · have heq : h x = none ↔ k x = none := by
      rw [← mem_unrevealed, ← mem_unrevealed, hhk]
    rw [mem_unrevealed, mem_unrevealed]
    change Function.update h e (some a) x = none ↔ Function.update k e (some b) x = none
    rw [Function.update_of_ne hx, Function.update_of_ne hx]
    exact heq

lemma run_map_fst
    {μ : PMF (E → Bool)} {hμ : ∀ ω, μ ω ≠ 0}
    (step : Assignment E → Assignment E → E → PMF (Bool × Bool))
    (next : Assignment E → E)
    (hfst : ∀ h k e, h e = none → (step h k e).map Prod.fst = bit μ hμ h e)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (h k : Assignment E) (hhk : unrevealed h = unrevealed k)
    (n : ℕ) (hn : (unrevealed h).card = n) :
    (run step next h k n).map (fun z => decodeOption z.1) = cond μ hμ h := by
  induction n generalizing h k with
  | zero =>
      have he : unrevealed h = ∅ := Finset.card_eq_zero.1 hn
      rw [run, cond_eq_pure_of_unrevealed_eq_empty μ hμ he]
      exact PMF.pure_map (fun z : Assignment E × Assignment E => decodeOption z.1) (h, k)
  | succ n ih =>
      have hcard : (unrevealed h).card = n + 1 := hn
      have hkne : (unrevealed k).Nonempty := by
        rw [← hhk, Finset.nonempty_iff_ne_empty]
        intro he
        rw [he] at hcard
        simp at hcard
      let e := next k
      have hke : k e = none := hnext k hkne
      have hhe : h e = none := by
        apply mem_unrevealed.1
        rw [hhk]
        exact mem_unrevealed.2 hke
      have hnew (a b : Bool) : unrevealed (reveal h e a) = unrevealed (reveal k e b) := by
        have hc := congrArg (fun s : Finset E => s.erase e) hhk
        simpa [unrevealed_reveal hhe, unrevealed_reveal hke] using hc
      have hnum (a b : Bool) : (unrevealed (reveal h e a)).card = n := by
        have hc := card_unrevealed_reveal hhe a
        omega
      rw [run, PMF.map_bind]
      calc
        _ = (step h k e).bind (fun z => cond μ hμ (reveal h e z.1)) := by
          congr 1
          funext z
          exact ih _ _ (hnew z.1 z.2) (hnum z.1 z.2)
        _ = ((step h k e).map Prod.fst).bind
            (fun b => cond μ hμ (reveal h e b)) := by rw [PMF.bind_map]; rfl
        _ = (bit μ hμ h e).bind (fun b => cond μ hμ (reveal h e b)) := by rw [hfst h k e hhe]
        _ = cond μ hμ h := bind_bit_cond hhe μ hμ

lemma run_map_snd
    {ν : PMF (E → Bool)} {hν : ∀ ω, ν ω ≠ 0}
    (step : Assignment E → Assignment E → E → PMF (Bool × Bool))
    (next : Assignment E → E)
    (hsnd : ∀ h k e, k e = none → (step h k e).map Prod.snd = bit ν hν k e)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (h k : Assignment E) (hhk : unrevealed h = unrevealed k)
    (n : ℕ) (hn : (unrevealed k).card = n) :
    (run step next h k n).map (fun z => decodeOption z.2) = cond ν hν k := by
  induction n generalizing h k with
  | zero =>
      have he : unrevealed k = ∅ := Finset.card_eq_zero.1 hn
      rw [run, cond_eq_pure_of_unrevealed_eq_empty ν hν he]
      exact PMF.pure_map (fun z : Assignment E × Assignment E => decodeOption z.2) (h, k)
  | succ n ih =>
      have hcard : (unrevealed k).card = n + 1 := hn
      have hkne : (unrevealed k).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he] at hcard
        simp at hcard
      let e := next k
      have hke : k e = none := hnext k hkne
      have hhe : h e = none := by
        apply mem_unrevealed.1
        rw [hhk]
        exact mem_unrevealed.2 hke
      have hnew (a b : Bool) : unrevealed (reveal h e a) = unrevealed (reveal k e b) := by
        have hc := congrArg (fun s : Finset E => s.erase e) hhk
        simpa [unrevealed_reveal hhe, unrevealed_reveal hke] using hc
      have hnum (a b : Bool) : (unrevealed (reveal k e b)).card = n := by
        have hc := card_unrevealed_reveal hke b
        omega
      rw [run, PMF.map_bind]
      calc
        _ = (step h k e).bind (fun z => cond ν hν (reveal k e z.2)) := by
          congr 1
          funext z
          exact ih _ _ (hnew z.1 z.2) (hnum z.1 z.2)
        _ = ((step h k e).map Prod.snd).bind
            (fun b => cond ν hν (reveal k e b)) := by rw [PMF.bind_map]; rfl
        _ = (bit ν hν k e).bind (fun b => cond ν hν (reveal k e b)) := by rw [hsnd h k e hke]
        _ = cond ν hν k := bind_bit_cond hke ν hν

lemma run_ordered
    (step : Assignment E → Assignment E → E → PMF (Bool × Bool))
    (next : Assignment E → E)
    (hstep : ∀ h k e, h e = none → k e = none → ∀ z, z ∈ (step h k e).support → z.1 ≤ z.2)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (h k : Assignment E) (hhk : unrevealed h = unrevealed k)
    (hle : decodeOption h ≤ decodeOption k)
    (n : ℕ) (hn : (unrevealed h).card = n)
    {z : Assignment E × Assignment E} (hz : z ∈ (run step next h k n).support) :
    decodeOption z.1 ≤ decodeOption z.2 := by
  induction n generalizing h k z with
  | zero =>
      have heq : z = (h, k) := (PMF.mem_support_pure_iff _ _).1 hz
      subst z
      exact hle
  | succ n ih =>
      have hcard : (unrevealed h).card = n + 1 := hn
      have hkne : (unrevealed k).Nonempty := by
        rw [← hhk, Finset.nonempty_iff_ne_empty]
        intro he
        rw [he] at hcard
        simp at hcard
      let e := next k
      have hke : k e = none := hnext k hkne
      have hhe : h e = none := by
        apply mem_unrevealed.1
        rw [hhk]
        exact mem_unrevealed.2 hke
      have hnew (a b : Bool) : unrevealed (reveal h e a) = unrevealed (reveal k e b) := by
        have hc := congrArg (fun s : Finset E => s.erase e) hhk
        simpa [unrevealed_reveal hhe, unrevealed_reveal hke] using hc
      have hnum (a b : Bool) : (unrevealed (reveal h e a)).card = n := by
        have hc := card_unrevealed_reveal hhe a
        omega
      rw [run, PMF.mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      exact ih _ _ (hnew w.1 w.2) (decodeOption_reveal_le hle
        (hstep h k e hhe hke w hw)) (hnum w.1 w.2) hz

/-- The empty assignment. -/
def blank : Assignment E := fun _ => none

@[simp] lemma unrevealed_blank : unrevealed (blank : Assignment E) = Finset.univ := by
  ext e
  simp [unrevealed, blank]

lemma cond_blank (μ : PMF (E → Bool)) (hμ : ∀ ω, μ ω ≠ 0) :
    cond μ hμ (blank : Assignment E) = μ := by
  apply PMF.ext
  intro ω
  rw [cond_apply]
  have hf : Fiber (blank : Assignment E) = Set.univ := by
    ext η
    constructor
    · intro _
      trivial
    · intro _ e b hb
      simp [blank] at hb
  have hm : mass μ (blank : Assignment E) = 1 := by
    rw [mass, hf]
    simpa only [Set.indicator_univ] using μ.tsum_coe
  rw [hf, Set.indicator_of_mem (Set.mem_univ _), hm, inv_one, mul_one]

/-- Adaptive selection preserves exact full-configuration marginals and pointwise
order.  This is the general probabilistic lemma behind exploration coupling. -/
structure AdaptiveCoupling (μ ν : PMF (E → Bool)) where
  dist : PMF ((E → Bool) × (E → Bool))
  map_fst : dist.map Prod.fst = μ
  map_snd : dist.map Prod.snd = ν
  ordered : ∀ z ∈ dist.support, z.1 ≤ z.2

/-- Construct an adaptive ordered coupling from any legal edge-selection strategy. -/
noncomputable def adaptiveCoupling
    {μ ν : PMF (E → Bool)} {hμ : ∀ ω, μ ω ≠ 0} {hν : ∀ ω, ν ω ≠ 0}
    (step : Assignment E → Assignment E → E → PMF (Bool × Bool))
    (next : Assignment E → E)
    (hfst : ∀ h k e, h e = none → (step h k e).map Prod.fst = bit μ hμ h e)
    (hsnd : ∀ h k e, k e = none → (step h k e).map Prod.snd = bit ν hν k e)
    (hstep : ∀ h k e, h e = none → k e = none → ∀ z, z ∈ (step h k e).support → z.1 ≤ z.2)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none) :
    AdaptiveCoupling μ ν where
  dist := (run step next blank blank (Fintype.card E)).map
    (fun z => (decodeOption z.1, decodeOption z.2))
  map_fst := by
    rw [PMF.map_comp]
    change (run step next blank blank (Fintype.card E)).map
      (fun z => decodeOption z.1) = μ
    rw [run_map_fst step next hfst hnext blank blank (by simp) _ (by simp)]
    exact cond_blank μ hμ
  map_snd := by
    rw [PMF.map_comp]
    change (run step next blank blank (Fintype.card E)).map
      (fun z => decodeOption z.2) = ν
    rw [run_map_snd step next hsnd hnext blank blank (by simp) _ (by simp)]
    exact cond_blank ν hν
  ordered := by
    intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact run_ordered step next hstep hnext blank blank (by simp) (by simp [decodeOption, blank])
      _ (by simp) hw

end FK.Adaptive
