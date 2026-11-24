import FK.ConfinedStrata
import FK.NestedCommonUpperGood

/-!
# Exploration-order free-interior continuation for region-confined nested graphs

This module supplies the finite free-boundary Markov step of Lemma 2.1 of
Beffara--Faipeur--Oke in the *ordinary nested* (non right-disjoint) geometry:
added labels may meet the smaller graph at the shell of the exploration region,
but every label incident to the region is a label of the smaller graph and is
already closed on the exploration stratum.

The key point formalised here is that the sequential FK/Bernoulli coupling
(`fkUpperOrderedCoupling`) realises the paper's inward exploration only when the
enumeration reveals the *region-exterior* labels first.  For that enumeration we
prove that the continuation of the larger FK after the exterior history is the
free FK law inside the region, for an arbitrary region-confined boundary
setoid.  The free-interior identity is the restricted-stratum theorem
`stratum_conditional_region_eq_region` transported to the exploration order.
-/

open scoped ENNReal NNReal BigOperators Classical

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary
open FK.RegionConfinement FK.RegionConfinement.ConfinedStrata
open FK.Exploration.Sequential FK.Exploration.StoppedInterior
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.Exploration.MaximalStrata FK.Exploration.RightWiredGood FK.Exploration.TwoSidedInterior
open FK.Exploration.NestedCoupledGood

namespace FK.NestedRegionExploration

variable {W K : Type*} [Fintype W] [Fintype K]

/-! ## The exterior-first exploration order of `Fin m ⊕ (Fin k ⊕ Fin a)` -/

/-- The exploration enumeration: first the `k` exterior (shell) labels of the
smaller graph, then its `m` region labels, then the `a` added labels. -/
noncomputable def annFirstEquiv (m k a : ℕ) :
    Fin (k + (m + a)) ≃ Fin m ⊕ (Fin k ⊕ Fin a) :=
  (((finSumFinEquiv (m := k) (n := m + a)).symm.trans
      (Equiv.sumCongr (Equiv.refl (Fin k)) (finSumFinEquiv (m := m) (n := a)).symm)).trans
    (Equiv.sumAssoc (Fin k) (Fin m) (Fin a)).symm).trans
    ((Equiv.sumCongr (Equiv.sumComm (Fin k) (Fin m)) (Equiv.refl (Fin a))).trans
      (Equiv.sumAssoc (Fin m) (Fin k) (Fin a)))

/-- Position of the `i`-th shell label. -/
def annPos {m k a : ℕ} (i : Fin k) : Fin (k + (m + a)) :=
  Fin.castAdd (m + a) i

/-- Position of the `j`-th region label. -/
def regPos {m k a : ℕ} (j : Fin m) : Fin (k + (m + a)) :=
  Fin.natAdd k (Fin.castAdd a j)

/-- Position of the `l`-th added label. -/
def addPos {m k a : ℕ} (l : Fin a) : Fin (k + (m + a)) :=
  Fin.natAdd k (Fin.natAdd m l)

@[simp] lemma annFirstEquiv_ann (m k a : ℕ) (i : Fin k) :
    annFirstEquiv m k a (annPos i) = Sum.inr (Sum.inl i) := by
  simp [annFirstEquiv, annPos]

@[simp] lemma annFirstEquiv_reg (m k a : ℕ) (j : Fin m) :
    annFirstEquiv m k a (regPos j) = Sum.inl j := by
  simp [annFirstEquiv, regPos]

@[simp] lemma annFirstEquiv_add (m k a : ℕ) (l : Fin a) :
    annFirstEquiv m k a (addPos l) = Sum.inr (Sum.inr l) := by
  simp [annFirstEquiv, addPos]

/-! ## The larger region-confined split graph in exploration order -/

section Graph

variable {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
  (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)

/-- The larger split graph: the smaller box's shell and region labels together
with the added labels, all on the vertex type `W ⊕ K`. -/
noncomputable abbrev bigSplit : LabelledMultigraph :=
  ambientOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo))

/-- The larger graph in exploration order. -/
noncomputable abbrev bigIndexed : LabelledMultigraph :=
  (bigSplit si ti so xo ao bo).transport (Equiv.refl (W ⊕ K)) (annFirstEquiv m k a)

/-- The exploration-order graph is the indexed graph of the same enumeration. -/
lemma bigIndexed_eq_finIndexed :
    bigIndexed si ti so xo ao bo =
      finIndexedGraph (W ⊕ K) (k + (m + a))
        (fun i => (bigSplit si ti so xo ao bo).source (annFirstEquiv m k a i))
        (fun i => (bigSplit si ti so xo ao bo).target (annFirstEquiv m k a i)) :=
  rfl

/-- The boundary setoid of the larger graph in exploration order. -/
noncomputable abbrev bigBoundary (ζ : Setoid (W ⊕ K)) : Setoid (W ⊕ K) :=
  (bigSplit si ti so xo ao bo).transportBoundaryOf (Equiv.refl (W ⊕ K))
    (eE := annFirstEquiv m k a) ζ

/-- The configuration equivalence from the exploration order to the split graph. -/
noncomputable abbrev bigConfigEquiv :
    (Fin (k + (m + a)) → Bool) ≃ ((Fin m ⊕ (Fin k ⊕ Fin a)) → Bool) :=
  (bigSplit si ti so xo ao bo).transportConfig (Equiv.refl (W ⊕ K)) (annFirstEquiv m k a)

end Graph

/-! ## Coordinate extraction -/

/-- Region coordinates of an exploration-order configuration. -/
def regionOfAnn {m k a : ℕ} (ω : Fin (k + (m + a)) → Bool) : Fin m → Bool :=
  fun j => ω (regPos j)

/-- Shell coordinates of an exploration-order configuration. -/
def annOfAnn {m k a : ℕ} (ω : Fin (k + (m + a)) → Bool) : Fin k → Bool :=
  fun i => ω (annPos i)

/-- The shell configuration recorded by a list of length `k`. -/
def annOfList (k : ℕ) (x : List Bool) : Fin k → Bool := fun i => x.getD i.1 false

/-- The separated shell stratum: exterior configurations whose shell
coordinates equal a prescribed list. -/
def shellStratum (k a : ℕ) (x : List Bool) : Set (Fin k ⊕ Fin a → Bool) :=
  {e | e ∘ Sum.inl = annOfList k x}

theorem prefixCylinder_coord_iff {n : ℕ} (x : List Bool) (ω : Fin n → Bool)
    (hx : x.length ≤ n) :
    ω ∈ prefixCylinder x ↔
      ∀ i : Fin x.length, ω ⟨i.1, lt_of_lt_of_le i.2 hx⟩ = x.getD i.1 false := by
  rw [prefixCylinder, Set.mem_ofPred_eq, List.prefix_iff_getElem]
  constructor
  · rintro ⟨h1, h2⟩ i
    have h3 := h2 i.1 i.2
    rw [List.getElem_ofFn] at h3
    rw [List.getD_eq_getElem x false i.2]
    exact h3.symm
  · intro h
    refine ⟨by simpa using hx, ?_⟩
    intro i hi
    have h3 : ω ⟨i, lt_of_lt_of_le hi hx⟩ = x.getD i false := h ⟨i, hi⟩
    rw [List.getD_eq_getElem x false hi] at h3
    rw [List.getElem_ofFn]
    exact h3.symm

/-! ## Reading the exploration-order configuration on the split graph -/

section Read

variable {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
  (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)

@[simp] lemma annFirstEquiv_symm_ann (m k a : ℕ) (i : Fin k) :
    (annFirstEquiv m k a).symm (Sum.inr (Sum.inl i)) = annPos i := by
  rw [Equiv.symm_apply_eq]
  simp

@[simp] lemma annFirstEquiv_symm_reg (m k a : ℕ) (j : Fin m) :
    (annFirstEquiv m k a).symm (Sum.inl j) = regPos j := by
  rw [Equiv.symm_apply_eq]
  simp

@[simp] lemma annFirstEquiv_symm_add (m k a : ℕ) (l : Fin a) :
    (annFirstEquiv m k a).symm (Sum.inr (Sum.inr l)) = addPos l := by
  rw [Equiv.symm_apply_eq]
  simp

lemma bigConfigEquiv_ann (ω : Fin (k + (m + a)) → Bool) (i : Fin k) :
    bigConfigEquiv si ti so xo ao bo ω (Sum.inr (Sum.inl i)) = annOfAnn ω i := by
  show ω ((annFirstEquiv m k a).symm (Sum.inr (Sum.inl i))) = annOfAnn ω i
  rw [annFirstEquiv_symm_ann]
  rfl

lemma bigConfigEquiv_reg (ω : Fin (k + (m + a)) → Bool) (j : Fin m) :
    bigConfigEquiv si ti so xo ao bo ω (Sum.inl j) = regionOfAnn ω j := by
  show ω ((annFirstEquiv m k a).symm (Sum.inl j)) = regionOfAnn ω j
  rw [annFirstEquiv_symm_reg]
  rfl

lemma bigConfigEquiv_add (ω : Fin (k + (m + a)) → Bool) (l : Fin a) :
    bigConfigEquiv si ti so xo ao bo ω (Sum.inr (Sum.inr l)) =
      ω (addPos l) := by
  show ω ((annFirstEquiv m k a).symm (Sum.inr (Sum.inr l))) = ω (addPos l)
  rw [annFirstEquiv_symm_add]

/-- On the exploration order, the prefix cylinder of a list of length `k` is
exactly the event that the shell coordinates equal that list. -/
theorem prefixCylinder_big (x : List Bool) (hx : x.length = k) :
    prefixCylinder x =
      {ω | bigConfigEquiv si ti so xo ao bo ω ∈
        extMask (I := Fin m) (shellStratum k a x)} := by
  ext ω
  rw [Set.mem_ofPred_eq, mem_extMask, shellStratum, Set.mem_ofPred_eq]
  rw [prefixCylinder_coord_iff x ω (by omega)]
  constructor
  · intro h
    funext i
    simp only [Function.comp_apply]
    rw [bigConfigEquiv_ann]
    exact h (Fin.cast hx.symm i)
  · intro h i
    have h2 := congrFun h (Fin.cast hx i)
    simp only [Function.comp_apply] at h2
    rw [bigConfigEquiv_ann] at h2
    exact h2

/-- Preimage form of the exploration prefix cylinder. -/
theorem prefixCylinder_big_preimage (x : List Bool) (hx : x.length = k) :
    prefixCylinder x =
      (bigConfigEquiv si ti so xo ao bo) ⁻¹'
        extMask (I := Fin m) (shellStratum k a x) := by
  rw [prefixCylinder_big si ti so xo ao bo x hx]
  rfl

end Read

end FK.NestedRegionExploration

/-! ## The continuation of the larger FK after the shell history -/

namespace FK.NestedRegionExploration

/-- The support proof argument of `PMF.filter` is immaterial. -/
lemma PMF.filter_congr_proof {α : Type*} (p : PMF α) (s : Set α)
    {h1 h2 : ∃ a ∈ s, a ∈ p.support} : p.filter s h1 = p.filter s h2 := by
  apply PMF.ext
  intro a
  simp only [PMF.filter_apply]

/-- Filtering is compatible with equal underlying laws. -/
lemma filter_congr_pmf {α : Type*} {p q : PMF α} (h : p = q) (s : Set α)
    (hp : ∃ a ∈ s, a ∈ p.support) (hq : ∃ a ∈ s, a ∈ q.support) :
    p.filter s hp = q.filter s hq := by
  subst h
  exact PMF.filter_congr_proof _ _

/-- Transporting a filtered law along a bijection of the state spaces. -/
lemma map_filter_equiv' {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (p : PMF A)
    {S : Set A} {T : Set B} (hST : ∀ a, a ∈ S ↔ e a ∈ T)
    (hA : ∃ a ∈ S, a ∈ p.support) (hB : ∃ b ∈ T, b ∈ (p.map e).support) :
    (p.filter S hA).map e = (p.map e).filter T hB := by
  have hmap : ∀ a, (p.map e) (e a) = p a := fun a => by
    have h := map_apply_of_injective e.injective p a
    simpa using h
  have hind : ∀ a, T.indicator (⇑(p.map e)) (e a) = S.indicator (⇑p) a := by
    intro a
    by_cases ha : a ∈ S
    · have ha' : e a ∈ T := (hST a).mp ha
      rw [Set.indicator_of_mem ha', Set.indicator_of_mem ha, hmap]
    · have ha' : e a ∉ T := fun h => ha ((hST a).mpr h)
      rw [Set.indicator_of_notMem ha', Set.indicator_of_notMem ha]
  have hsum : (∑' b, T.indicator (⇑(p.map e)) b) = ∑' a, S.indicator (⇑p) a := by
    rw [tsum_fintype, tsum_fintype]
    exact (Fintype.sum_equiv e (fun a => S.indicator (⇑p) a)
      (fun b => T.indicator (⇑(p.map e)) b) (fun a => (hind a).symm)).symm
  apply PMF.ext
  intro b
  have hlhs : ((p.filter S hA).map e) b = (p.filter S hA) (e.symm b) := by
    have h := map_apply_of_injective e.injective (p.filter S hA) (e.symm b)
    simpa using h
  rw [hlhs, PMF.filter_apply, PMF.filter_apply, hsum]
  have hb : b ∈ T ↔ e.symm b ∈ S := by
    rw [hST (e.symm b)]
    simp
  have hmapb : (p.map e) b = p (e.symm b) := by
    have h := map_apply_of_injective e.injective p (e.symm b)
    simpa using h
  by_cases h : b ∈ T
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hb.mp h), hmapb]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hh => h (hb.mpr hh))]

/-- The shell stratum is nonempty. -/
lemma shellStratum_nonempty {k a : ℕ} (x : List Bool) :
    (shellStratum k a x).Nonempty :=
  ⟨Sum.elim (annOfList k x) (fun _ => false), by funext i; rfl⟩

/-- Every shell stratum consists of separated exterior configurations. -/
lemma shellStratum_sep {m k a : ℕ} {W K : Type*} [Fintype W] [Fintype K]
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) {x : List Bool}
    (havoid : AddedAvoid ao bo)
    (hxsep : SmallSep so xo (annOfList k x)) :
    ∀ e ∈ shellStratum k a x, ExtSep so xo ao bo e := by
  intro e he l hl
  cases l with
  | inl i => exact hxsep i (by rw [← congrFun he i]; exact hl)
  | inr j => exact havoid j

/-- **Exploration continuation, general form.**  For any law `μ` on the
exploration order whose split-graph pushforward is the larger FK law, the
region coordinates after the shell history are distributed as the free region
law. -/
theorem extendLower_shellHistory_eq_region_aux {W K : Type*} [Fintype W] [Fintype K]
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : AddedAvoid ao bo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (x : List Bool) (hxlen : x.length = k)
    (hxsep : SmallSep so xo (annOfList k x))
    (μ : PMF (Fin (k + (m + a)) → Bool)) (hμ : ∀ ω, μ ω ≠ 0)
    (hmap : PMF.map (bigConfigEquiv si ti so xo ao bo) μ =
      (bigSplit si ti so xo ao bo).fkPMF hq hp₁.le ζ) :
    PMF.map (fun l : List Bool => regionOfAnn (toConfig (k + (m + a)) l))
      (extendLower (canonicalNext μ hμ) x (m + a)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  have hlen : x.length + (m + a) = k + (m + a) := by omega
  have hsA : ∃ (a' : Fin (k + (m + a)) → Bool),
      a' ∈ prefixCylinder x ∧ a' ∈ μ.support :=
    prefixCylinder_support_of_positive μ hμ x (by omega)
  have hchain :
      PMF.map (fun l : List Bool => regionOfAnn (toConfig (k + (m + a)) l))
        (extendLower (canonicalNext μ hμ) x (m + a)) =
      (μ.filter (prefixCylinder x) hsA).map (fun ω => regionOfAnn ω) := by
    rw [extendLower_canonicalNext _ _ x (m + a) hlen, PMF.map_comp]
    have hcomp : (fun l : List Bool => regionOfAnn (toConfig (k + (m + a)) l)) ∘
        (List.ofFn : (Fin (k + (m + a)) → Bool) → List Bool) =
          (fun ω => regionOfAnn ω) := by
      funext ω
      exact congrArg regionOfAnn (toConfig_ofFn ω)
    rw [hcomp]
    try exact (congrArg (fun R => PMF.map (fun ω => regionOfAnn ω) R)
      (PMF.filter_congr_proof _ _))
  rw [hchain]
  have hreg : (fun ω : Fin (k + (m + a)) → Bool => regionOfAnn ω) =
      (fun ω => interiorConfig (bigConfigEquiv si ti so xo ao bo ω)) := by
    funext ω j
    exact (bigConfigEquiv_reg si ti so xo ao bo ω j).symm
  rw [hreg]
  rw [show (fun ω : Fin (k + (m + a)) → Bool =>
        interiorConfig (bigConfigEquiv si ti so xo ao bo ω))
      = interiorConfig ∘ (bigConfigEquiv si ti so xo ao bo) from rfl]
  rw [← PMF.map_comp]
  have hsB : ∃ b ∈ extMask (I := Fin m) (shellStratum k a x),
      b ∈ (PMF.map (bigConfigEquiv si ti so xo ao bo) μ).support := by
    rw [hmap]
    exact extMask_support (I := Fin m) si ti so xo ao bo ζ hq hp₀ hp₁
      (shellStratum k a x) (shellStratum_nonempty x)
  have hP : prefixCylinder x = (bigConfigEquiv si ti so xo ao bo) ⁻¹'
      extMask (I := Fin m) (shellStratum k a x) :=
    prefixCylinder_big_preimage si ti so xo ao bo x hxlen
  have hPT : ∀ a' : Fin (k + (m + a)) → Bool,
      a' ∈ prefixCylinder x ↔
        a' ∈ (bigConfigEquiv si ti so xo ao bo) ⁻¹'
          extMask (I := Fin m) (shellStratum k a x) := by
    intro a'
    rw [hP]
  have hstep : (μ.filter (prefixCylinder x) hsA).map (bigConfigEquiv si ti so xo ao bo) =
      (μ.map (bigConfigEquiv si ti so xo ao bo)).filter
        (extMask (I := Fin m) (shellStratum k a x)) hsB :=
    map_filter_equiv' (bigConfigEquiv si ti so xo ao bo) μ
      (fun a' => by simpa using hPT a') hsA hsB
  rw [hstep]
  have hsB' : ∃ b ∈ extMask (I := Fin m) (shellStratum k a x),
      b ∈ ((bigSplit si ti so xo ao bo).fkPMF hq hp₁.le ζ).support :=
    extMask_support (I := Fin m) si ti so xo ao bo ζ hq hp₀ hp₁
      (shellStratum k a x) (shellStratum_nonempty x)
  have hmapf : (PMF.map (bigConfigEquiv si ti so xo ao bo) μ).filter
        (extMask (I := Fin m) (shellStratum k a x)) hsB =
      ((bigSplit si ti so xo ao bo).fkPMF hq hp₁.le ζ).filter
        (extMask (I := Fin m) (shellStratum k a x)) hsB' :=
    filter_congr_pmf hmap _ hsB hsB'
  rw [hmapf]
  have hstr := stratum_conditional_region_eq_region (I := Fin m) si ti so xo ao bo θ ζ
    hconf hθ hq hp₀ hp₁ (shellStratum k a x)
    (shellStratum_sep (m := m) so xo ao bo havoid hxsep) (shellStratum_nonempty x)
  exact (congrArg (fun R => PMF.map interiorConfig R)
    (PMF.filter_congr_proof _ _)).trans hstr

/-- **Exploration continuation** for the actual FK law of the larger graph in
exploration order. -/
theorem extendLower_shellHistory_eq_region {W K : Type*} [Fintype W] [Fintype K]
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : AddedAvoid ao bo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (x : List Bool) (hxlen : x.length = k)
    (hxsep : SmallSep so xo (annOfList k x)) :
    PMF.map (fun l : List Bool => regionOfAnn (toConfig (k + (m + a)) l))
      (extendLower (canonicalNext
        ((bigIndexed si ti so xo ao bo).fkPMF hq hp₁.le (bigBoundary si ti so xo ao bo ζ))
        (fun ω => fkPMF_ne_zero (bigIndexed si ti so xo ao bo) hq hp₀ hp₁
          (bigBoundary si ti so xo ao bo ζ) ω)) x (m + a)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ :=
  extendLower_shellHistory_eq_region_aux si ti so xo ao bo θ ζ hconf hθ havoid hq hp₀ hp₁
    x hxlen hxsep _ _ (map_transport_fkPMF (bigSplit si ti so xo ao bo) (Equiv.refl (W ⊕ K))
      (eE := annFirstEquiv m k a) ζ hq hp₀ hp₁)

end FK.NestedRegionExploration

/-! ## The FK/Bernoulli pair law of the larger graph -/

namespace FK.NestedRegionExploration

section PairLaw

variable {W K : Type*} [Fintype W] [Fintype K]

/-- The larger graph in exploration order, as an indexed graph. -/
noncomputable abbrev bigPairSource {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) : Fin (k + (m + a)) → W ⊕ K :=
  fun i => (bigSplit si ti so xo ao bo).source (annFirstEquiv m k a i)

/-- Target map of the larger graph in exploration order. -/
noncomputable abbrev bigPairTarget {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) : Fin (k + (m + a)) → W ⊕ K :=
  fun i => (bigSplit si ti so xo ao bo).target (annFirstEquiv m k a i)

lemma bigIndexed_eq_pairGraph {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) :
    bigIndexed si ti so xo ao bo =
      finIndexedGraph (W ⊕ K) (k + (m + a)) (bigPairSource si ti so xo ao bo)
        (bigPairTarget si ti so xo ao bo) :=
  rfl

/-- The actual FK law of the larger graph in exploration order. -/
noncomputable def bigPairLaw {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₁ : p < 1) : PMF (Fin (k + (m + a)) → Bool) :=
  (finIndexedGraph (W ⊕ K) (k + (m + a)) (bigPairSource si ti so xo ao bo)
    (bigPairTarget si ti so xo ao bo)).fkPMF hq hp₁.le
      (bigBoundary si ti so xo ao bo ζ)

lemma bigPairLaw_ne_zero {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ω : Fin (k + (m + a)) → Bool) :
    bigPairLaw si ti so xo ao bo ζ hq hp₁ ω ≠ 0 :=
  fkPMF_ne_zero (finIndexedGraph (W ⊕ K) (k + (m + a))
    (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo))
    hq hp₀ hp₁ (bigBoundary si ti so xo ao bo ζ) ω

/-- The pair law's pushforward to the split graph is the actual FK law there. -/
theorem map_bigConfigEquiv_bigPairLaw {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (bigConfigEquiv si ti so xo ao bo)
        (bigPairLaw si ti so xo ao bo ζ hq hp₁) =
      (bigSplit si ti so xo ao bo).fkPMF hq hp₁.le ζ := by
  rw [bigPairLaw]
  exact map_transport_fkPMF (bigSplit si ti so xo ao bo) (Equiv.refl (W ⊕ K))
    (eE := annFirstEquiv m k a) ζ hq hp₀ hp₁

end PairLaw

end FK.NestedRegionExploration

/-! ## Pair-level continuation after the shell phase -/

namespace FK.NestedRegionExploration

section PairContinuation

variable {W K : Type*} [Fintype W] [Fintype K]

/-- The ordered FK/Bernoulli step of the larger graph in exploration order. -/
noncomputable abbrev bigStep {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    List Bool → List Bool → PMF (Bool × Bool) :=
  orderedUpperStep (bigPairLaw si ti so xo ao bo ζ hq hp₁)
    (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁) (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le)
    (fun x => fk_upper_nextBound (bigPairSource si ti so xo ao bo)
      (bigPairTarget si ti so xo ao bo) (bigBoundary si ti so xo ao bo ζ) hq hp₀ hp₁ x)

lemma bigStep_map_fst {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (x y : List Bool) :
    (bigStep si ti so xo ao bo ζ hq hp₀ hp₁ x y).map Prod.fst =
      canonicalNext (bigPairLaw si ti so xo ao bo ζ hq hp₁)
        (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁) x :=
  (boolOrderedCouplingOfLe (canonicalNext (bigPairLaw si ti so xo ao bo ζ hq hp₁)
    (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁) x) (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) _).map_fst

lemma bigStep_ordered {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (x y : List Bool)
    {z : Bool × Bool} (hz : z ∈ (bigStep si ti so xo ao bo ζ hq hp₀ hp₁ x y).support) :
    z.1 ≤ z.2 :=
  (boolOrderedCouplingOfLe (canonicalNext (bigPairLaw si ti so xo ao bo ζ hq hp₁)
    (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁) x) (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) _).ordered z hz

lemma bigStep_map_snd {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (x y : List Bool) :
    (bigStep si ti so xo ao bo ζ hq hp₀ hp₁ x y).map Prod.snd =
      FKModel.bernoulliPMF (upperRateNN q p) (upperRateNN_le_one hq hp₁.le) :=
  (boolOrderedCouplingOfLe (canonicalNext (bigPairLaw si ti so xo ao bo ζ hq hp₁)
    (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁) x) (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) _).map_snd

/-- **Pair exploration continuation.**  For a separated shell configuration of
the smaller graph, the larger FK/Bernoulli pair continues, in the region
coordinates, with the free region law. -/
theorem pair_interior_continuation_bigAnn {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : AddedAvoid ao bo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    {ρ : Fin m ⊕ Fin k → Bool}
    (hρ : Separated si ti so xo (exteriorConfig ρ))
    {x y : List Bool}
    (hxy : (x, y) ∈ (extendPair (bigStep si ti so xo ao bo ζ hq hp₀ hp₁) [] [] k).support)
    (hy : y = exteriorHistory ρ) :
    (extendPair (bigStep si ti so xo ao bo ζ hq hp₀ hp₁) x y (m + a)).map
        (fun z => regionOfAnn (toConfig (k + (m + a)) z.1)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  have hlen := extendPair_length_support (bigStep si ti so xo ao bo ζ hq hp₀ hp₁) [] [] k hxy
  have hxlen : x.length = k := by simpa using hlen.1
  have hord := extendPair_ordered (bigStep si ti so xo ao bo ζ hq hp₀ hp₁)
    (fun x y z hz => bigStep_ordered si ti so xo ao bo ζ hq hp₀ hp₁ x y hz)
    List.Forall₂.nil k hxy
  have hxle : toConfig k x ≤ toConfig k y := toConfig_le_of_forall₂ (n := k) hord
  have hxsep : SmallSep so xo (annOfList k x) := by
    intro i hi
    have hxi : toConfig k x i = true := hi
    have hyi : toConfig k y i = true := by
      have h := hxle i
      rw [hxi] at h
      cases hb : toConfig k y i with
      | false => rw [hb] at h; exact absurd h (by simp)
      | true => rfl
    have hyi' : toConfig k y i = y.getD i.1 false := rfl
    rw [hyi', hy, List.getD_eq_getElem _ _ (by simp [exteriorHistory])] at hyi
    simp only [exteriorHistory, List.getElem_ofFn] at hyi
    obtain ⟨hso, hxo⟩ := hρ i hyi
    exact ⟨fun h => hso (inRegion_iff.mp h), fun h => hxo (inRegion_iff.mp h)⟩
  have h1 : (extendPair (bigStep si ti so xo ao bo ζ hq hp₀ hp₁) x y (m + a)).map
        (fun z => regionOfAnn (toConfig (k + (m + a)) z.1)) =
      ((extendPair (bigStep si ti so xo ao bo ζ hq hp₀ hp₁) x y (m + a)).map
        Prod.fst).map (fun ω => regionOfAnn (toConfig (k + (m + a)) ω)) := by
    rw [PMF.map_comp]
    rfl
  have h2 : (extendPair (bigStep si ti so xo ao bo ζ hq hp₀ hp₁) x y (m + a)).map Prod.fst =
      extendLower (canonicalNext (bigPairLaw si ti so xo ao bo ζ hq hp₁)
        (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁)) x (m + a) :=
    extendPair_map_fst (bigStep si ti so xo ao bo ζ hq hp₀ hp₁)
      (canonicalNext (bigPairLaw si ti so xo ao bo ζ hq hp₁)
        (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁))
      (fun x y => bigStep_map_fst si ti so xo ao bo ζ hq hp₀ hp₁ x y) x y (m + a)
  have h3 : (extendLower (canonicalNext (bigPairLaw si ti so xo ao bo ζ hq hp₁)
        (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁)) x (m + a)).map
        (fun ω => regionOfAnn (toConfig (k + (m + a)) ω)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ :=
    extendLower_shellHistory_eq_region_aux si ti so xo ao bo θ ζ hconf hθ havoid
      hq hp₀ hp₁ x hxlen hxsep (bigPairLaw si ti so xo ao bo ζ hq hp₁)
      (bigPairLaw_ne_zero si ti so xo ao bo ζ hq hp₀ hp₁)
      (map_bigConfigEquiv_bigPairLaw si ti so xo ao bo ζ hq hp₀ hp₁)
  exact h1.trans (h2 ▸ h3)

end PairContinuation

end FK.NestedRegionExploration

/-! ## Good intersections for the shell-first exploration order -/

namespace FK.NestedRegionExploration

local instance : MeasurableSpace (List Bool × List Bool) := ⊤

/-- The shell-separation event read from a history list. -/
def shellSep {W K : Type*} {m k : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (y : List Bool) : Prop :=
  Separated si ti so xo (fun i : Fin k => y.getD i.1 false)

/-- The shell-separation event depends only on the shell coordinates. -/
lemma shellSep_congr {W K : Type*} {m k : ℕ} {si : Fin m → W} {ti : Fin m → W}
    {so xo : Fin k → W ⊕ K} {x y : List Bool}
    (heq : (fun i : Fin k => x.getD i.1 false) = (fun i : Fin k => y.getD i.1 false)) :
    shellSep si ti so xo x ↔ shellSep si ti so xo y := by
  rw [shellSep, shellSep, heq]

lemma shellSep_of_prefix {W K : Type*} {m k : ℕ} {si : Fin m → W} {ti : Fin m → W}
    {so xo : Fin k → W ⊕ K} {x y : List Bool} (hx : x.length = k) (h : x <+: y) :
    shellSep si ti so xo x ↔ shellSep si ti so xo y := by
  have heq : toConfig k x = toConfig k y := toConfig_eq_of_prefix hx h
  have heq' : (fun i : Fin k => x.getD i.1 false) = (fun i : Fin k => y.getD i.1 false) := heq
  constructor <;> intro h' <;> (rw [shellSep] at *)
  · rwa [← heq']
  · rwa [heq']

theorem shellSep_ambientOfHistory {W K : Type*} {m k : ℕ} {si : Fin m → W} {ti : Fin m → W}
    {so xo : Fin k → W ⊕ K} {y : List Bool} :
    shellSep si ti so xo y ↔
      Separated si ti so xo (exteriorConfig (ambientOfHistory (m := m) (k := k) y)) := by
  have hext : exteriorConfig (ambientOfHistory (m := m) (k := k) y) =
      (fun i : Fin k => y.getD i.1 false) := by
    funext i
    rfl
  rw [shellSep, hext]

/-- **Good intersection for the shell-first exploration order.**  The larger
FK/Bernoulli pair (with the added labels after the smaller box's shell and
region labels) and the smaller pair have the same intersection mass with a
region event and the shell-separation stratum. -/
theorem good_intersection_annFirst {W K : Type*} [Fintype W] [Fintype K] {m k a : ℕ}
    (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS ζL : Setoid K)
    (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : AddedAvoid ao bo) (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) :
    let T := transportedAmbient si ti so xo
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (W ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let μS : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξS
    let hμS : ∀ ω, μS ω ≠ 0 := fun ω => fkPMF_ne_zero T hq hp₀ hp₁ ξS ω
    let stepS := orderedUpperStep μS hμS (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
      (fun x => fk_upper_nextBound _ _ ξS hq hp₀ hp₁ x)
    let stepB := bigStep si ti so xo ao bo ζB hq hp₀ hp₁
    (extendPair stepB [] [] (k + (m + a))).toMeasure
        {w : List Bool × List Bool |
          regionOfAnn (toConfig (k + (m + a)) w.1) ∈ A ∧ shellSep si ti so xo w.2} =
      (extendPair stepS [] [] (k + m)).toMeasure
        {w : List Bool × List Bool |
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A ∧
            shellSep si ti so xo w.2} := by
  intro T G ξS μS hμS stepS stepB
  let pfxS := extendPair stepS [] [] k
  let pfxB := extendPair stepB [] [] k
  let remS : List Bool × List Bool → PMF (List Bool × List Bool) :=
    fun z => extendPair stepS z.1 z.2 m
  let remB : List Bool × List Bool → PMF (List Bool × List Bool) :=
    fun z => extendPair stepB z.1 z.2 (m + a)
  let free : PMF (Fin m → Bool) := (regionGraph si ti).fkPMF hq hp₁.le θ
  let F : List Bool → ℝ≥0∞ := fun y => if shellSep si ti so xo y then free.toMeasure A else 0
  let EL : Set (List Bool × List Bool) :=
    {w | regionOfAnn (toConfig (k + (m + a)) w.1) ∈ A ∧ shellSep si ti so xo w.2}
  let ES : Set (List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A ∧
      shellSep si ti so xo w.2}
  have hdecompS : extendPair stepS [] [] (k + m) = pfxS.bind remS :=
    extendPair_add stepS [] [] k m
  have hdecompB : extendPair stepB [] [] (k + (m + a)) = pfxB.bind remB := by
    simpa only [pfxB, remB, Nat.add_assoc] using extendPair_add stepB [] [] k (m + a)
  rw [hdecompB, hdecompS,
    PMF.toMeasure_bind_apply _ _ EL MeasurableSet.of_discrete,
    PMF.toMeasure_bind_apply _ _ ES MeasurableSet.of_discrete]
  have hShellEq : ∀ {z w : List Bool × List Bool}, z.2.length = k →
      z.2 <+: w.2 →
      ((fun i : Fin k => w.2.getD i.1 false) = fun i : Fin k => z.2.getD i.1 false) := by
    intro z w hz2 hp
    funext i
    exact (congrFun (toConfig_eq_of_prefix hz2 hp) i).symm
  have hB (z : List Bool × List Bool) : pfxB z * (remB z).toMeasure EL = pfxB z * F z.2 := by
    by_cases hz : z ∈ pfxB.support
    · have hlen := extendPair_length_support stepB [] [] k hz
      have hz2len : z.2.length = k := by simpa using hlen.2
      have hprefix : ∀ {w : List Bool × List Bool}, w ∈ (remB z).support → z.2 <+: w.2 :=
        fun hw => (extendPair_prefix_support stepB z.1 z.2 (m + a) hw).2
      by_cases hM : shellSep si ti so xo z.2
      · have hρ : Separated si ti so xo
            (exteriorConfig (ambientOfHistory (m := m) (k := k) z.2)) :=
          (shellSep_ambientOfHistory).mp hM
        have hcont := pair_interior_continuation_bigAnn si ti so xo ao bo θ ζB hconf hθ
          havoid hq hp₀ hp₁ hρ (x := z.1) (y := z.2) hz
          (exteriorHistory_ambientOfHistory (m := m) hz2len).symm
        have hstable : ∀ w ∈ (remB z).support,
            (w ∈ EL ↔ regionOfAnn (toConfig (k + (m + a)) w.1) ∈ A) := by
          intro w hw
          have heq := hShellEq hz2len (hprefix hw)
          constructor
          · intro h; exact h.1
          · intro h
            exact ⟨h, (shellSep_congr heq).mpr hM⟩
        calc pfxB z * (remB z).toMeasure EL =
              pfxB z * (remB z).toMeasure
                {w | regionOfAnn (toConfig (k + (m + a)) w.1) ∈ A} := by
                rw [pmf_toMeasure_eq_of_support (remB z) EL _ hstable]
                rfl
          _ = pfxB z * ((remB z).map
                (fun w => regionOfAnn (toConfig (k + (m + a)) w.1))).toMeasure A := by
                rw [toMeasure_map_pmf _ _ _ measurable_from_top MeasurableSet.of_discrete]
                rfl
          _ = pfxB z * free.toMeasure A := by rw [hcont]
          _ = pfxB z * F z.2 := by simp [F, hM]
      · have hzero : (remB z).toMeasure EL = 0 := by
          calc (remB z).toMeasure EL = (remB z).toMeasure ∅ := by
                apply pmf_toMeasure_eq_of_support
                intro w hw
                have heq := hShellEq hz2len (hprefix hw)
                constructor
                · intro h
                  exact hM ((shellSep_congr heq).mp h.2)
                · intro h; exact h.elim
            _ = 0 := by simp
        simp [hzero, F, hM]
    · have hz0 : pfxB z = 0 := (PMF.apply_eq_zero_iff _ _).2 hz
      simp [hz0]
  have hS (z : List Bool × List Bool) : pfxS z * (remS z).toMeasure ES = pfxS z * F z.2 := by
    by_cases hz : z ∈ pfxS.support
    · have hlen := extendPair_length_support stepS [] [] k hz
      have hz2len : z.2.length = k := by simpa using hlen.2
      have hprefix : ∀ {w : List Bool × List Bool}, w ∈ (remS z).support → z.2 <+: w.2 :=
        fun hw => (extendPair_prefix_support stepS z.1 z.2 m hw).2
      by_cases hM : shellSep si ti so xo z.2
      · have hρ : ambientOfHistory (m := m) (k := k) z.2 ∈
            maximalSplitStratum si ti so xo :=
          (mem_maximalSplitStratum_iff si ti so xo _ hright).mpr
            ((shellSep_ambientOfHistory).mp hM)
        have hcont := pair_interior_continuation_twoSided si ti so xo hq hp₀ hp₁
          θ ζS (ambientOfHistory z.2) hright hρ (x := z.1) (y := z.2) hz
          (exteriorHistory_ambientOfHistory (m := m) hz2len).symm
        have hstable : ∀ w ∈ (remS z).support,
            (w ∈ ES ↔ interiorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.1)) ∈ A) := by
          intro w hw
          have heq := hShellEq hz2len (hprefix hw)
          constructor
          · intro h; exact h.1
          · intro h
            exact ⟨h, (shellSep_congr heq).mpr hM⟩
        calc pfxS z * (remS z).toMeasure ES =
              pfxS z * (remS z).toMeasure
                {w | interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A} := by
                rw [pmf_toMeasure_eq_of_support (remS z) ES _ hstable]
                rfl
          _ = pfxS z * ((remS z).map (fun w =>
                interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)))).toMeasure A := by
                rw [toMeasure_map_pmf _ _ _ measurable_from_top MeasurableSet.of_discrete]
                rfl
          _ = pfxS z * free.toMeasure A := by rw [hcont]
          _ = pfxS z * F z.2 := by simp [F, hM]
      · have hzero : (remS z).toMeasure ES = 0 := by
          calc (remS z).toMeasure ES = (remS z).toMeasure ∅ := by
                apply pmf_toMeasure_eq_of_support
                intro w hw
                have heq := hShellEq hz2len (hprefix hw)
                constructor
                · intro h
                  exact hM ((shellSep_congr heq).mp h.2)
                · intro h; exact h.elim
            _ = 0 := by simp
        simp [hzero, F, hM]
    · have hz0 : pfxS z = 0 := (PMF.apply_eq_zero_iff _ _).2 hz
      simp [hz0]
  have hsndS : ∀ x y, (stepS x y).map Prod.snd =
      FKModel.bernoulliPMF (upperRateNN q p) (upperRateNN_le_one hq hp₁.le) := by
    intro x y
    exact (boolOrderedCouplingOfLe (canonicalNext μS hμS x) (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le) _).map_snd
  have hsndB : ∀ x y, (stepB x y).map Prod.snd =
      FKModel.bernoulliPMF (upperRateNN q p) (upperRateNN_le_one hq hp₁.le) :=
    fun x y => bigStep_map_snd si ti so xo ao bo ζB hq hp₀ hp₁ x y
  have hpS : pfxS.map Prod.snd =
      extendLower (fun _ => FKModel.bernoulliPMF (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)) [] k :=
    extendPair_map_snd stepS _ hsndS [] [] k
  have hpB : pfxB.map Prod.snd =
      extendLower (fun _ => FKModel.bernoulliPMF (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)) [] k :=
    extendPair_map_snd stepB _ hsndB [] [] k
  calc (∑' z, pfxB z * (remB z).toMeasure EL) = ∑' z, pfxB z * F z.2 :=
        tsum_congr hB
    _ = ∑' z, pfxS z * F z.2 :=
        tsum_pair_weight_eq_of_map_snd_general pfxB pfxS _ hpB hpS F
    _ = ∑' z, pfxS z * (remS z).toMeasure ES := (tsum_congr hS).symm

end FK.NestedRegionExploration

/-! ## Configuration-level good intersections -/

namespace FK.NestedRegionExploration

/-- The region part of a smaller-box configuration in exterior-first order. -/
def smallRegion {k m : ℕ} (y : Fin (k + m) → Bool) : Fin m → Bool :=
  fun j => y (Fin.natAdd k j)

lemma exteriorFirst_symm_inl {m k : ℕ} (j : Fin m) :
    (exteriorFirst (m := m) (k := k)).symm (Sum.inl j) = Fin.natAdd k j := by
  simp [exteriorFirst, finSumFinEquiv]

lemma interiorConfig_toAmbientConfig_smallRegion {W K : Type*} [Fintype W] [Fintype K]
    {m k : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (y : Fin (k + m) → Bool) :
    interiorConfig (toAmbientConfig si ti so xo y) = smallRegion y := by
  funext j
  show toAmbientConfig si ti so xo y (Sum.inl j) = y (Fin.natAdd k j)
  rw [show toAmbientConfig si ti so xo y (Sum.inl j) =
    y ((exteriorFirst (m := m) (k := k)).symm (Sum.inl j)) from rfl]
  rw [exteriorFirst_symm_inl]

lemma exteriorConfig_toAmbientConfig_smallRegion {W K : Type*} [Fintype W] [Fintype K]
    {m k : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (y : Fin (k + m) → Bool) :
    exteriorConfig (toAmbientConfig si ti so xo y) = fun i : Fin k => y (Fin.castAdd m i) := by
  funext i
  rfl

/-- A one-vertex graph carrying the `a` added labels. -/
noncomputable abbrev dummyGO (a : ℕ) : LabelledMultigraph where
  Vertex := PUnit
  Edge := Fin a
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit

/-- The smaller graph in exterior-first order, as an indexed graph. -/
noncomputable abbrev smallIdx {W K : Type*} [Fintype W] [Fintype K] {m k : ℕ}
    (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K) : LabelledMultigraph :=
  finIndexedGraph (W ⊕ K) (k + m) (transportedAmbient si ti so xo).source
    (transportedAmbient si ti so xo).target

lemma smallIdx_eq_transported {W K : Type*} [Fintype W] [Fintype K] {m k : ℕ}
    (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K) :
    smallIdx si ti so xo = transportedAmbient si ti so xo := rfl

/-- The nested edge equivalence for the shell-first exploration order. -/
noncomputable def nestedExploreEquiv (m k a : ℕ) :
    Fin (k + m) ⊕ Fin a ≃ Fin (k + (m + a)) :=
  (finSumFinEquiv (m := k + m) (n := a)).trans (Fin.castOrderIso (by omega)).toEquiv

@[simp] lemma nestedExploreEquiv_inl {m k a : ℕ} (j : Fin (k + m)) :
    nestedExploreEquiv m k a (Sum.inl j) = ⟨j.1, by omega⟩ := by
  simp [nestedExploreEquiv, finSumFinEquiv]
  exact Fin.ext rfl

@[simp] lemma nestedExploreEquiv_inr {m k a : ℕ} (l : Fin a) :
    nestedExploreEquiv m k a (Sum.inr l) = ⟨k + m + l.1, by omega⟩ := by
  simp [nestedExploreEquiv, finSumFinEquiv]
  exact Fin.ext rfl

lemma nestedExploreEquiv_apply_inl {m k a : ℕ} (ω : Fin (k + (m + a)) → Bool)
    (j : Fin (k + m)) :
    ω (nestedExploreEquiv m k a (Sum.inl j)) = ω ⟨j.1, by omega⟩ := by
  rw [nestedExploreEquiv_inl]

end FK.NestedRegionExploration

namespace FK.NestedRegionExploration

local instance : MeasurableSpace (List Bool × List Bool) := ⊤

/-- The concrete shell-plus-region restriction of an exploration-order
configuration to the smaller box. -/
def restrictSmall (k m a : ℕ) (ω : Fin (k + (m + a)) → Bool) : Fin (k + m) → Bool :=
  fun j => ω ⟨j.1, by omega⟩

/-- **Configuration-level good intersection for the shell-first order.** -/
theorem good_intersection_annFirstPairs {W K : Type*} [Fintype W] [Fintype K]
    {m k a : ℕ}
    (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS ζL : Setoid K)
    (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : AddedAvoid ao bo) (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) :
    let T := transportedAmbient si ti so xo
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (W ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let ξB : Setoid (W ⊕ K) := bigBoundary si ti so xo ao bo ζB
    let B : Set (Fin (k + (m + a)) → Bool) := {ω | regionOfAnn ω ∈ A}
    let AD : Set (Fin (k + m) → Bool) := {y | smallRegion y ∈ A}
    let C : Set (Fin (k + m) → Bool) :=
      {ρ | Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}
    (fkUpperPair (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
        ξB hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictSmall k m a ⁻¹' C)) =
      (fkUpperPair T.source T.target ξS hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) := by
  intro T G ξS ξB B AD C
  let N := k + (m + a)
  let decodeB : List Bool × List Bool → (Fin N → Bool) × (Fin N → Bool) :=
    fun w => (toConfig N w.1, toConfig N w.2)
  let decodeS : List Bool × List Bool → (Fin (k + m) → Bool) × (Fin (k + m) → Bool) :=
    fun w => (toConfig (k + m) w.1, toConfig (k + m) w.2)
  let EL : Set (List Bool × List Bool) :=
    {w | regionOfAnn (toConfig N w.1) ∈ A ∧ shellSep si ti so xo w.2}
  let ES : Set (List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A ∧
      shellSep si ti so xo w.2}
  have hCext : ∀ (w : List Bool × List Bool),
      exteriorConfig (toAmbientConfig si ti so xo
        (restrictSmall k m a (toConfig N w.2))) = fun i : Fin k => w.2.getD i.1 false := by
    intro w
    funext i
    rw [exteriorConfig_toAmbientConfig_smallRegion]
    rfl
  have hL : decodeB ⁻¹' (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictSmall k m a ⁻¹' C)) = EL := by
    ext w
    have hCs : (restrictSmall k m a (toConfig N w.2) ∈ C) ↔ shellSep si ti so xo w.2 := by
      show Separated si ti so xo
        (exteriorConfig (toAmbientConfig si ti so xo
          (restrictSmall k m a (toConfig N w.2)))) ↔ _
      rw [hCext w, shellSep]
    exact and_congr Iff.rfl hCs
  have hS : decodeS ⁻¹' (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) = ES := by
    ext w
    have h1 : (toConfig (k + m) w.1 ∈ AD) ↔
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A := by
      show smallRegion (toConfig (k + m) w.1) ∈ A ↔ _
      rw [← interiorConfig_toAmbientConfig_smallRegion si ti so xo]
    have h2 : (toConfig (k + m) w.2 ∈ C) ↔ shellSep si ti so xo w.2 := by
      show Separated si ti so xo
        (exteriorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2))) ↔ _
      have hext : exteriorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2)) =
          (fun i : Fin k => w.2.getD i.1 false) := by
        funext i
        rw [exteriorConfig_toAmbientConfig_smallRegion]
        rfl
      rw [hext, shellSep]
    exact and_congr h1 h2
  have hmapB : (upperHistoryPair (bigPairLaw si ti so xo ao bo ζB hq hp₁)
      (bigPairLaw_ne_zero si ti so xo ao bo ζB hq hp₀ hp₁) (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le)
      (fun x => fk_upper_nextBound (bigPairSource si ti so xo ao bo)
        (bigPairTarget si ti so xo ao bo) ξB hq hp₀ hp₁ x) N).map decodeB =
      fkUpperPair (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
        ξB hq hp₀ hp₁ := rfl
  have hmapS : (upperHistoryPair (T.fkPMF hq hp₁.le ξS)
      (fkPMF_ne_zero T hq hp₀ hp₁ ξS) (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le)
      (fun x => fk_upper_nextBound T.source T.target ξS hq hp₀ hp₁ x) (k + m)).map decodeS =
      fkUpperPair T.source T.target ξS hq hp₀ hp₁ := rfl
  have hhist := good_intersection_annFirst si ti so xo ao bo θ ζS ζL ζB hconf hθ havoid
    hright hq hp₀ hp₁ A
  have step1 : (fkUpperPair (bigPairSource si ti so xo ao bo)
        (bigPairTarget si ti so xo ao bo) ξB hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictSmall k m a ⁻¹' C)) =
      (upperHistoryPair (bigPairLaw si ti so xo ao bo ζB hq hp₁)
        (bigPairLaw_ne_zero si ti so xo ao bo ζB hq hp₀ hp₁) (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)
        (fun x => fk_upper_nextBound (bigPairSource si ti so xo ao bo)
          (bigPairTarget si ti so xo ao bo) ξB hq hp₀ hp₁ x) N).toMeasure
        (decodeB ⁻¹' (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictSmall k m a ⁻¹' C))) := by
    rw [← hmapB]
    exact toMeasure_map_pmf decodeB _ _ measurable_from_top MeasurableSet.of_discrete
  have step2 : (upperHistoryPair (bigPairLaw si ti so xo ao bo ζB hq hp₁)
        (bigPairLaw_ne_zero si ti so xo ao bo ζB hq hp₀ hp₁) (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)
        (fun x => fk_upper_nextBound (bigPairSource si ti so xo ao bo)
          (bigPairTarget si ti so xo ao bo) ξB hq hp₀ hp₁ x) N).toMeasure
        (decodeB ⁻¹' (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictSmall k m a ⁻¹' C))) =
      (upperHistoryPair (T.fkPMF hq hp₁.le ξS) (fkPMF_ne_zero T hq hp₀ hp₁ ξS)
        (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
        (fun x => fk_upper_nextBound T.source T.target ξS hq hp₀ hp₁ x) (k + m)).toMeasure ES := by
    rw [hL]
    with_unfolding_all exact hhist
  have step3 : (upperHistoryPair (T.fkPMF hq hp₁.le ξS) (fkPMF_ne_zero T hq hp₀ hp₁ ξS)
        (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
        (fun x => fk_upper_nextBound T.source T.target ξS hq hp₀ hp₁ x) (k + m)).toMeasure ES =
      (fkUpperPair T.source T.target ξS hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) := by
    rw [← hS]
    rw [← toMeasure_map_pmf decodeS _ (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C)
      measurable_from_top MeasurableSet.of_discrete]
    rw [hmapS]
  exact step1.trans (step2.trans step3)

end FK.NestedRegionExploration


/-! ## Axiom audit of the principal exports -/

#print axioms FK.NestedRegionExploration.extendLower_shellHistory_eq_region_aux
#print axioms FK.NestedRegionExploration.extendLower_shellHistory_eq_region
#print axioms FK.NestedRegionExploration.pair_interior_continuation_bigAnn
#print axioms FK.NestedRegionExploration.good_intersection_annFirst
#print axioms FK.NestedRegionExploration.good_intersection_annFirstPairs
#print axioms FK.NestedRegionExploration.prefixCylinder_big
#print axioms FK.NestedRegionExploration.map_bigConfigEquiv_bigPairLaw
