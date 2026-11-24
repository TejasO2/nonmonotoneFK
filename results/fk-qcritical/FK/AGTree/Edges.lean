import FK.AGTree.Graph
import CurvatureVariance.Infra.EfronStein.Coordinates
import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Edge coordinates, the product law, and block independence
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

/-- Child pointers: a vertex together with a letter that may be appended. -/
abbrev Echild : Type := {p : V × A // p.1.Valid p.2}

instance : DecidableEq Echild := Subtype.instDecidableEq

/-- The edge determined by a child pointer. -/
def childE (x : Echild) : G.edgeSet :=
  ⟨s(x.1.1, x.1.1.snoc x.1.2 x.2), (SimpleGraph.mem_edgeSet G).2 (adj_snoc x.2)⟩

lemma childE_inj : Function.Injective childE := by
  rintro ⟨⟨v, a⟩, hv⟩ ⟨⟨u, b⟩, hu⟩ h
  have h' : s(v, v.snoc a hv) = s(u, u.snoc b hu) := Subtype.ext_iff.1 h
  have hv' : (v.snoc a hv).w = v.w ++ [a] := rfl
  have hu' : (u.snoc b hu).w = u.w ++ [b] := rfl
  rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : v.w ++ [a] = u.w ++ [b] := by rw [← hv', ← hu', h2]
    have hvu : v = u := h1
    have hab : a = b := by
      have := congrArg List.getLast? h3
      simpa using this
    subst hvu; subst hab
    rfl
  · exfalso
    have e1 : v.w.length = u.w.length + 1 := by rw [h1, V.snoc_length]
    have e2 : v.w.length + 1 = u.w.length := by rw [← h2, V.snoc_length]
    omega

lemma childE_surj : Function.Surjective childE := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ v w =>
    have hadj : G.Adj v w := (SimpleGraph.mem_edgeSet G).1 he
    rcases adj_iff.1 hadj with ⟨a, hv, rfl⟩ | ⟨hne, rfl⟩
    · exact ⟨⟨(v, a), hv⟩, rfl⟩
    · have hpv : (v.parent hne).snoc (v.w.getLast hne) (valid_of_append (by
          rw [V.parent_w, List.dropLast_append_getLast hne]; exact v.red)) = v := by
        apply V.ext
        simp [V.snoc_w, V.parent_w, List.dropLast_append_getLast]
      refine ⟨⟨(v.parent hne, v.w.getLast hne), ?_⟩, ?_⟩
      · exact valid_of_append (by rw [V.parent_w, List.dropLast_append_getLast hne]; exact v.red)
      · apply Subtype.ext
        show s(v.parent hne, (v.parent hne).snoc (v.w.getLast hne) _) = s(v, v.parent hne)
        rw [hpv]
        exact Sym2.eq_swap

/-- The edge set is exactly the set of child pointers. -/
noncomputable def edgeEquiv : Echild ≃ G.edgeSet := Equiv.ofBijective childE ⟨childE_inj, childE_surj⟩

@[simp] lemma edgeEquiv_apply (x : Echild) : edgeEquiv x = childE x := rfl

lemma edgeEquiv_symm_childE (x : Echild) : edgeEquiv.symm (childE x) = x := by
  rw [Equiv.symm_apply_eq]
  rfl

/-- The letter class of an edge. -/
noncomputable def letterOf (e : G.edgeSet) : A := (edgeEquiv.symm e).1.2

lemma letterOf_childE (x : Echild) : letterOf (childE x) = x.1.2 := by
  simp only [letterOf, edgeEquiv_symm_childE]

lemma childE_valid (v : V) (a : A) (h : v.Valid a) : letterOf (childE ⟨(v, a), h⟩) = a :=
  letterOf_childE _

/-- The open probability of an edge. -/
noncomputable def edgeRate (r : Fin 2 → unitInterval) : G.edgeSet → unitInterval :=
  fun e => r (acls (letterOf e))

lemma edgeRate_childE (r : Fin 2 → unitInterval) (v : V) (a : A) (h : v.Valid a) :
    edgeRate r (childE (⟨(v, a), h⟩ : Echild)) = r (acls a) := by
  rw [edgeRate, letterOf_childE]

/-- **The two-class bond percolation law**: independent edges, class-`0` letters open with
probability `r 0`, class-`1` letters with probability `r 1`. -/
noncomputable abbrev law (r : Fin 2 → unitInterval) : Measure (G.edgeSet → Bool) :=
  Measure.infinitePi (fun e => bernoulliMeasure true false (r (acls (letterOf e))))

instance (r : Fin 2 → unitInterval) : IsProbabilityMeasure (law r) := by
  unfold law; infer_instance

lemma measurableSet_coord (e : G.edgeSet) : MeasurableSet {ω : G.edgeSet → Bool | ω e = true} :=
  measurableSet_eq_fun (measurable_pi_apply e) measurable_const

lemma law_coord (r : Fin 2 → unitInterval) (e : G.edgeSet) :
    law r {ω : G.edgeSet → Bool | ω e = true} =
      ENNReal.ofReal ((r (acls (letterOf e)) : ℝ)) := by
  have h := (measurePreserving_eval_infinitePi
    (fun e : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf e)))) e).measure_preimage
    (measurableSet_singleton true).nullMeasurableSet
  have hb : bernoulliMeasure true false (r (acls (letterOf e))) {true} =
      ENNReal.ofReal ((r (acls (letterOf e)) : ℝ)) := by
    rw [← bernoulliMeasure_real_apply_of_mem_of_notMem (x := true) (y := false)
      (r (acls (letterOf e))) (measurableSet_singleton true) rfl (by simp), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [law]
  exact h.trans hb

/-- An event depends only on the coordinates in `D`. -/
def DependsOn {ι : Type*} (A : Set (ι → Bool)) (D : Set ι) : Prop :=
  ∀ ω η : ι → Bool, (∀ i ∈ D, ω i = η i) → (ω ∈ A ↔ η ∈ A)

open Classical in
/-- Extend a configuration on `D` by closed coordinates outside `D`. -/
noncomputable def extendFalse {ι : Type*} (D : Set ι) (η : D → Bool) : ι → Bool :=
  fun i => if h : i ∈ D then η ⟨i, h⟩ else false

lemma measurable_extendFalse {ι : Type*} (D : Set ι) : Measurable (extendFalse D) := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ D
  · simp only [extendFalse, h, dite_true]
    exact measurable_pi_apply _
  · simp only [extendFalse, h, dite_false]
    exact measurable_const

lemma extendFalse_domRestrict {ι : Type*} (D : Set ι) (ω : ι → Bool) {i : ι} (hi : i ∈ D) :
    extendFalse D (D.domRestrict ω) i = ω i := by
  simp [extendFalse, hi, Set.domRestrict]

lemma eq_preimage_restrict_of_dependsOn {ι : Type*} {A : Set (ι → Bool)} {D : Set ι}
    (h : DependsOn A D) : A = D.domRestrict ⁻¹' (extendFalse D ⁻¹' A) := by
  ext ω
  simp only [Set.mem_preimage]
  exact h _ _ fun i hi => (extendFalse_domRestrict D ω hi).symm

/-- **Independence of events depending on pairwise disjoint blocks of coordinates.** -/
theorem measure_iInter_eq_prod {ι : Type*} (m : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (m i)] {κ : Type*} [Fintype κ]
    (A : κ → Set (ι → Bool)) (D : κ → Set ι)
    (hdisj : Pairwise (fun k l => Disjoint (D k) (D l)))
    (hmeas : ∀ k, MeasurableSet (A k)) (hdep : ∀ k, DependsOn (A k) (D k)) :
    Measure.infinitePi m (⋂ k, A k) = ∏ k, Measure.infinitePi m (A k) := by
  classical
  have hind : ProbabilityTheory.iIndepFun (fun k (ω : ι → Bool) => fun j : D k => ω j)
      (Measure.infinitePi m) :=
    CurvatureVariance.Infra.EfronStein.iIndepFun_comp_restrict_infinitePi m D hdisj
      (fun k => id) (fun k => measurable_id)
  have hres := ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.1 hind
    (Finset.univ (α := κ)) (sets := fun k => extendFalse (D k) ⁻¹' A k)
    (fun k _ => (hmeas k).preimage (measurable_extendFalse (D k)))
  have hAk : ∀ k, A k = (fun ω : ι → Bool => fun j : D k => ω j) ⁻¹'
      (extendFalse (D k) ⁻¹' A k) := fun k => eq_preimage_restrict_of_dependsOn (hdep k)
  have hpt : ∀ (k : κ) (ω : ι → Bool),
      (ω ∈ A k ↔ extendFalse (D k) (fun j : D k => ω j) ∈ A k) :=
    fun k ω => (hdep k) ω _ (fun i hi => (extendFalse_domRestrict (D k) ω hi).symm)
  have hL : (⋂ k, A k) = ⋂ k ∈ Finset.univ,
      (fun ω : ι → Bool => fun j : D k => ω j) ⁻¹' (extendFalse (D k) ⁻¹' A k) := by
    ext ω
    simp only [Set.mem_iInter, Finset.mem_univ, true_implies, Set.mem_preimage]
    exact ⟨fun h k => (hpt k ω).1 (h k), fun h k => (hpt k ω).2 (h k)⟩
  have hR : (∏ k, Measure.infinitePi m (A k)) = ∏ k,
      Measure.infinitePi m ((fun ω : ι → Bool => fun j : D k => ω j) ⁻¹'
        (extendFalse (D k) ⁻¹' A k)) := by
    refine Finset.prod_congr rfl (fun k _ => ?_)
    congr 1
    ext ω
    simpa using (hpt k ω)
  rw [hL, hR]
  exact hres

end Ultra
