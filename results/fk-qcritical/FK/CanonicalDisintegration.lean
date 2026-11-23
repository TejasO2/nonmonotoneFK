import FK.ExplorationSequential
import FK.FiniteComparison

/-!
# Canonical sequential disintegration of a positive finite law

For a pointwise-positive PMF on `Fin n → Bool`, conditioning on successively
longer prefixes supplies a sequential conditional kernel.  Reconstructing the
configuration by that kernel returns the original law, and after conditioning
on a prefix it returns the corresponding filtered law.
-/

namespace FK.Exploration.Sequential

open scoped ENNReal BigOperators Classical

/-- The cylinder of configurations whose `List.ofFn` presentation begins
with the history `x`. -/
def prefixCylinder {n : ℕ} (x : List Bool) : Set (Fin n → Bool) :=
  {ω | x <+: List.ofFn ω}

/-- The next coordinate, with a default outside the valid prefix lengths. -/
def nextCoord {n : ℕ} (ω : Fin n → Bool) (k : ℕ) : Bool :=
  (List.ofFn ω).getD k false

lemma getD_ofFn {n : ℕ} (ω : Fin n → Bool) {k : ℕ} (hk : k < n) :
    (List.ofFn ω).getD k false = ω ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  exact List.getElem_ofFn _

/-- A one-bit-longer prefix is equivalent to the old prefix together with the
specified value of the next coordinate. -/
lemma prefix_append_bit_iff {n : ℕ} (ω : Fin n → Bool) (x : List Bool)
    (b : Bool) (hk : x.length < n) :
    x ++ [b] <+: List.ofFn ω ↔
      x <+: List.ofFn ω ∧ b = ω ⟨x.length, hk⟩ := by
  constructor
  · intro h
    have hx : x <+: List.ofFn ω := (List.prefix_append x [b]).trans h
    refine ⟨hx, ?_⟩
    have hb := h.getElem (i := x.length) (by simp)
    simpa using hb
  · rintro ⟨hx, rfl⟩
    have h := List.concat_get_prefix hx (by simpa using hk)
    simpa using h

/-- A canonical full configuration extending a prefix. -/
def extendFn {n : ℕ} (x : List Bool) (hx : x.length ≤ n) : Fin n → Bool :=
  fun i => if h : i.1 < x.length then x[i.1] else false

lemma prefix_extendFn {n : ℕ} (x : List Bool) (hx : x.length ≤ n) :
    x <+: List.ofFn (extendFn x hx) := by
  rw [List.prefix_iff_getElem]
  refine ⟨by simpa using hx, ?_⟩
  intro i hi
  simp only [List.getElem_ofFn, extendFn, dif_pos hi]

lemma prefixCylinder_support_of_positive {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (hx : x.length ≤ n) :
    ∃ ω ∈ prefixCylinder x, ω ∈ μ.support := by
  refine ⟨extendFn x hx, prefix_extendFn x hx, (PMF.mem_support_iff _ _).mpr (hμ _)⟩

/-- The exact conditional law of the next coordinate given a prefix. -/
noncomputable def nextBit {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (hx : x.length < n) : PMF Bool :=
  (μ.filter (prefixCylinder x) (prefixCylinder_support_of_positive μ hμ x hx.le)).map
    (fun ω => nextCoord ω x.length)

/-- A total sequential kernel, with an irrelevant fallback at invalid
prefix lengths. -/
noncomputable def canonicalNext {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) : PMF Bool :=
  if hx : x.length < n then nextBit μ hμ x hx else PMF.pure false

/-- Unnormalized mass of a prefix cylinder. -/
noncomputable def cylMass {n : ℕ} (μ : PMF (Fin n → Bool)) (x : List Bool) : ℝ≥0∞ :=
  ∑' ω, (prefixCylinder x).indicator (⇑μ) ω

lemma cylMass_ne_top {n : ℕ} (μ : PMF (Fin n → Bool)) (x : List Bool) :
    cylMass μ x ≠ ⊤ := by
  have hle : cylMass μ x ≤ ∑' ω, μ ω := by
    apply ENNReal.tsum_le_tsum
    intro ω
    by_cases h : ω ∈ prefixCylinder x <;> simp [Set.indicator, h]
  rw [μ.tsum_coe] at hle
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

lemma cylMass_pos_of_positive {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (hx : x.length ≤ n) :
    0 < cylMass μ x := by
  rw [cylMass, tsum_fintype]
  have hterm : 0 < (prefixCylinder x).indicator (⇑μ) (extendFn x hx) := by
    simp [prefixCylinder, prefix_extendFn x hx, pos_iff_ne_zero.mpr (hμ _)]
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (fun ω _ => (zero_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ (extendFn x hx)))

/-- Evaluation of a PMF transported by an injective map at a point in its
range. -/
lemma map_apply_of_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) (μ : PMF α) (a : α) :
    (μ.map f) (f a) = μ a := by
  rw [PMF.map_apply]
  calc
    _ = (if f a = f a then μ a else 0) := by
      apply tsum_eq_single a
      intro b hba
      by_cases heq : f a = f b
      · exact (hba (hf heq).symm).elim
      · simp [heq]
    _ = μ a := by simp

lemma map_injective_of_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) : Function.Injective (PMF.map f) := by
  intro μ ν h
  apply PMF.ext
  intro a
  rw [← map_apply_of_injective hf μ a, ← map_apply_of_injective hf ν a, h]

/-- The one-bit conditional is the ratio of the extended-prefix mass to the
current-prefix mass. -/
theorem nextBit_apply {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (hx : x.length < n) (b : Bool) :
    nextBit μ hμ x hx b = cylMass μ (x ++ [b]) * (cylMass μ x)⁻¹ := by
  unfold nextBit
  rw [PMF.map_apply]
  calc
    _ = ∑' ω, (prefixCylinder (x ++ [b])).indicator (⇑μ) ω *
          (cylMass μ x)⁻¹ := by
      apply tsum_congr
      intro ω
      rw [PMF.filter_apply]
      have hcoord : nextCoord ω x.length = ω ⟨x.length, hx⟩ := by
        unfold nextCoord
        exact getD_ofFn ω hx
      by_cases hlong : x ++ [b] <+: List.ofFn ω
      · obtain ⟨hshort, hb⟩ := (prefix_append_bit_iff ω x b hx).mp hlong
        have hnext : b = nextCoord ω x.length := hb.trans hcoord.symm
        have hs : ω ∈ prefixCylinder x := hshort
        have hl : ω ∈ prefixCylinder (x ++ [b]) := hlong
        rw [if_pos hnext, Set.indicator_of_mem hs, Set.indicator_of_mem hl]
        rfl
      · by_cases hnext : b = nextCoord ω x.length
        · have hshort : ¬ x <+: List.ofFn ω := by
            intro hs
            exact hlong ((prefix_append_bit_iff ω x b hx).mpr
              ⟨hs, hnext.trans hcoord⟩)
          have hs : ω ∉ prefixCylinder x := hshort
          have hl : ω ∉ prefixCylinder (x ++ [b]) := hlong
          rw [if_pos hnext, Set.indicator_of_notMem hs, Set.indicator_of_notMem hl]
          simp
        · have hl : ω ∉ prefixCylinder (x ++ [b]) := hlong
          rw [if_neg hnext, Set.indicator_of_notMem hl]
          simp
    _ = cylMass μ (x ++ [b]) * (cylMass μ x)⁻¹ := by
      rw [ENNReal.tsum_mul_right]
      rfl

/-- Maps which agree on the support of a PMF have the same pushforward. -/
lemma map_congr_support {α β : Type*} (μ : PMF α) {f g : α → β}
    (h : ∀ a ∈ μ.support, f a = g a) : μ.map f = μ.map g := by
  apply PMF.ext
  intro b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ μ.support
  · simp [h a ha]
  · have hzero : μ a = 0 := (PMF.apply_eq_zero_iff μ a).mpr ha
    simp [hzero]


/-- Revealing the canonical next bit and then conditioning on the extended
prefix is exactly conditioning on the original prefix. -/
theorem bind_nextBit_filter {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (hx : x.length < n) :
    (nextBit μ hμ x hx).bind (fun b =>
      μ.filter (prefixCylinder (x ++ [b]))
        (prefixCylinder_support_of_positive μ hμ (x ++ [b]) (by simp; omega))) =
      μ.filter (prefixCylinder x)
        (prefixCylinder_support_of_positive μ hμ x hx.le) := by
  apply PMF.ext
  intro ω
  rw [PMF.bind_apply, tsum_fintype]
  by_cases hP : ω ∈ prefixCylinder x
  · let b₀ : Bool := ω ⟨x.length, hx⟩
    have hnext : ∀ b, ω ∈ prefixCylinder (x ++ [b]) ↔ b = b₀ := by
      intro b
      rw [show ω ∈ prefixCylinder (x ++ [b]) ↔
        x <+: List.ofFn ω ∧ b = ω ⟨x.length, hx⟩ from
          prefix_append_bit_iff ω x b hx]
      exact and_iff_right hP
    calc
      (∑ b, nextBit μ hμ x hx b *
          (μ.filter (prefixCylinder (x ++ [b]))
            (prefixCylinder_support_of_positive μ hμ (x ++ [b]) (by simp; omega))) ω) =
          nextBit μ hμ x hx b₀ *
            (μ.filter (prefixCylinder (x ++ [b₀]))
              (prefixCylinder_support_of_positive μ hμ (x ++ [b₀]) (by simp; omega))) ω := by
        apply Finset.sum_eq_single b₀
        · intro b _ hb
          have hnot : ω ∉ prefixCylinder (x ++ [b]) := by
            rw [hnext]
            exact hb
          rw [PMF.filter_apply, Set.indicator_of_notMem hnot]
          simp
        · intro h
          simp at h
      _ = cylMass μ (x ++ [b₀]) * (cylMass μ x)⁻¹ *
          ((prefixCylinder (x ++ [b₀])).indicator (⇑μ) ω *
            (cylMass μ (x ++ [b₀]))⁻¹) := by
        rw [nextBit_apply, PMF.filter_apply]
        rfl
      _ = μ ω * (cylMass μ x)⁻¹ := by
        have hQ : ω ∈ prefixCylinder (x ++ [b₀]) := (hnext b₀).mpr rfl
        rw [Set.indicator_of_mem hQ]
        have hQ0 : cylMass μ (x ++ [b₀]) ≠ 0 :=
          ne_of_gt (cylMass_pos_of_positive μ hμ (x ++ [b₀]) (by simp; omega))
        have hQt : cylMass μ (x ++ [b₀]) ≠ ⊤ := cylMass_ne_top μ _
        calc
          _ = μ ω * (cylMass μ x)⁻¹ *
              (cylMass μ (x ++ [b₀]) * (cylMass μ (x ++ [b₀]))⁻¹) := by ac_rfl
          _ = _ := by rw [ENNReal.mul_inv_cancel hQ0 hQt, mul_one]
      _ = (μ.filter (prefixCylinder x)
          (prefixCylinder_support_of_positive μ hμ x hx.le)) ω := by
        rw [PMF.filter_apply, Set.indicator_of_mem hP]
        rfl
  · have hR : (μ.filter (prefixCylinder x)
        (prefixCylinder_support_of_positive μ hμ x hx.le)) ω = 0 := by
      rw [PMF.filter_apply, Set.indicator_of_notMem hP]
      simp
    rw [hR]
    apply Finset.sum_eq_zero
    intro b _
    have hQ : ω ∉ prefixCylinder (x ++ [b]) := by
      intro hmem
      exact hP ((prefix_append_bit_iff ω x b hx).mp hmem).1
    rw [PMF.filter_apply, Set.indicator_of_notMem hQ]
    simp

/-- **Prefix-filter chain rule.**  Sequentially sampling the remaining bits
with the canonical conditional kernel is exactly the pushforward of the
original law conditioned on the starting prefix. -/
theorem extendLower_canonicalNext {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (x : List Bool) (k : ℕ)
    (hxk : x.length + k = n) :
    extendLower (canonicalNext μ hμ) x k =
      (μ.filter (prefixCylinder x)
        (prefixCylinder_support_of_positive μ hμ x (by omega))).map List.ofFn := by
  induction k generalizing x with
  | zero =>
      have hlen : x.length = n := by omega
      let hsupp := prefixCylinder_support_of_positive μ hμ x (by omega)
      have hconst : ∀ ω ∈ (μ.filter (prefixCylinder x) hsupp).support,
          List.ofFn ω = x := by
        intro ω hω
        have hxω : ω ∈ prefixCylinder x :=
          ((PMF.mem_support_filter_iff hsupp).mp hω).1
        exact hxω.eq_of_length (by simpa [hlen]) |>.symm
      change PMF.pure x = (μ.filter (prefixCylinder x) hsupp).map List.ofFn
      rw [show (μ.filter (prefixCylinder x) hsupp).map List.ofFn =
          (μ.filter (prefixCylinder x) hsupp).map (Function.const _ x) by
        exact map_congr_support _ hconst]
      exact (PMF.map_const _ _).symm
  | succ k ih =>
      have hx : x.length < n := by omega
      simp only [extendLower, canonicalNext, dif_pos hx]
      calc
        (nextBit μ hμ x hx).bind (fun b =>
            extendLower (canonicalNext μ hμ) (x ++ [b]) k) =
            (nextBit μ hμ x hx).bind (fun b =>
              (μ.filter (prefixCylinder (x ++ [b]))
                (prefixCylinder_support_of_positive μ hμ (x ++ [b])
                  (by simp; omega))).map List.ofFn) := by
          congr 1
          funext b
          exact ih (x ++ [b]) (by simp; omega)
        _ = ((nextBit μ hμ x hx).bind (fun b =>
              μ.filter (prefixCylinder (x ++ [b]))
                (prefixCylinder_support_of_positive μ hμ (x ++ [b])
                  (by simp; omega)))).map List.ofFn := by
          rw [PMF.map_bind]
        _ = (μ.filter (prefixCylinder x)
            (prefixCylinder_support_of_positive μ hμ x (by omega))).map List.ofFn := by
          rw [bind_nextBit_filter μ hμ x hx]

/-- Reconstructing every coordinate from the empty prefix returns the original
finite law exactly. -/
theorem extendLower_canonicalNext_nil {n : ℕ} (μ : PMF (Fin n → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) :
    extendLower (canonicalNext μ hμ) [] n = μ.map List.ofFn := by
  have hcyl : prefixCylinder ([] : List Bool) =
      (Set.univ : Set (Fin n → Bool)) := by
    ext ω
    simp [prefixCylinder]
  have hf : μ.filter (prefixCylinder [])
      (prefixCylinder_support_of_positive μ hμ [] (by simp)) = μ := by
    apply PMF.ext
    intro ω
    rw [PMF.filter_apply]
    simp only [hcyl, Set.indicator_univ]
    rw [μ.tsum_coe]
    simp
  rw [extendLower_canonicalNext μ hμ [] n (by simp), hf]


/-- The same chain rule after mapping the injective `List.ofFn` presentation
back to the finite configuration type. -/
theorem extendLower_canonicalNext_ofFn_injective {n : ℕ}
    (μ : PMF (Fin n → Bool)) :
    Function.Injective (PMF.map (List.ofFn : (Fin n → Bool) → List Bool)) :=
  map_injective_of_injective List.ofFn_injective

end FK.Exploration.Sequential
