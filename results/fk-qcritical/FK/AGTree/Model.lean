import FK.AGTree.Fwd

/-!
# The branching recursion for the two-class tree
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

noncomputable abbrev pr (r : Fin 2 → unitInterval) (A : Set (G.edgeSet → Bool)) : ℝ :=
  (law r).real A

lemma pr_univ (r : Fin 2 → unitInterval) : pr r Set.univ = 1 := by
  rw [pr, measureReal_def, measure_univ, ENNReal.toReal_one]

lemma pr_nonneg (r : Fin 2 → unitInterval) (A : Set (G.edgeSet → Bool)) : 0 ≤ pr r A :=
  measureReal_nonneg

lemma pr_le_one (r : Fin 2 → unitInterval) (A : Set (G.edgeSet → Bool)) : pr r A ≤ 1 := by
  rw [pr, ← pr_univ r]
  exact measureReal_mono (Set.subset_univ A) (by simp)

lemma pr_coord (r : Fin 2 → unitInterval) (e : G.edgeSet) :
    pr r {ω : G.edgeSet → Bool | ω e = true} = (r (acls (letterOf e)) : ℝ) := by
  rw [pr, measureReal_def, law_coord, ENNReal.toReal_ofReal]
  exact unitInterval.nonneg _

/-- Two-block independence, in real arithmetic. -/
lemma pr_inter (r : Fin 2 → unitInterval) {A B : Set (G.edgeSet → Bool)}
    {D₁ D₂ : Set G.edgeSet} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdA : DependsOn A D₁) (hdB : DependsOn B D₂) (hdisj : Disjoint D₁ D₂) :
    pr r (A ∩ B) = pr r A * pr r B := by
  classical
  have h := measure_iInter_eq_prod
    (m := fun e : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf e))))
    (A := fun k : Bool => Bool.rec A B k) (D := fun k : Bool => Bool.rec D₁ D₂ k)
    (by
      intro k l hkl
      cases k <;> cases l
      · exact absurd rfl hkl
      · exact hdisj
      · exact hdisj.symm
      · exact absurd rfl hkl)
    (by intro k; cases k <;> assumption)
    (by intro k; cases k <;> assumption)
  have hset : (⋂ k : Bool, Bool.rec A B k) = A ∩ B := by
    ext ω; simp [Bool.forall_bool]
  have hprod : (∏ k : Bool,
      (Measure.infinitePi (fun e : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf e)))))
        (Bool.rec A B k)) =
      (Measure.infinitePi (fun e : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf e))))) A *
      (Measure.infinitePi (fun e : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf e))))) B := by
    rw [Fintype.prod_bool, mul_comm]
  rw [pr, pr, pr, measureReal_def, measureReal_def, measureReal_def, ← hset]
  show ((Measure.infinitePi
    (fun e : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf e)))))
      (⋂ k : Bool, Bool.rec A B k)).toReal = _
  rw [h, hprod, ENNReal.toReal_mul]

/-- The per-child "failure" event at level `n`. -/
def Ev (u : V) (n : ℕ) (a : A) : Set (G.edgeSet → Bool) :=
  {ω | ∀ (h : u.Valid a), ω (childE (⟨(u, a), h⟩ : Echild)) = false ∨
    ¬ Fwd ω (u.snoc a h) n}

/-- The coordinate block read by the failure event of one child. -/
noncomputable def Dblk (u : V) (a : A) : Set G.edgeSet :=
  if h : u.Valid a then
    ({childE (⟨(u, a), h⟩ : Echild)} : Set G.edgeSet) ∪ subE (u.snoc a h) else ∅

lemma ev_valid_eq (u : V) (a : A) (n : ℕ) (h : u.Valid a) :
    Ev u n a = ({ω | ω (childE (⟨(u, a), h⟩ : Echild)) = false} ∪
        {ω | ¬ Fwd ω (u.snoc a h) n}) := by
  ext ω
  simp only [Ev, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro hω; exact hω h
  · intro hω h'
    rw [show (⟨(u, a), h'⟩ : Echild) = ⟨(u, a), h⟩ from Subtype.ext rfl,
      show u.snoc a h' = u.snoc a h from V.ext rfl]
    exact hω

lemma ev_not_valid (u : V) (n : ℕ) {a : A} (h : ¬ u.Valid a) : Ev u n a = Set.univ := by
  ext ω
  simp only [Ev, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact fun hh => absurd hh h

lemma ev_compl_eq (u : V) (a : A) (n : ℕ) (h : u.Valid a) :
    (Ev u n a)ᶜ = ({ω : G.edgeSet → Bool | ω (childE (⟨(u, a), h⟩ : Echild)) = true} ∩
      {ω | Fwd ω (u.snoc a h) n}) := by
  rw [ev_valid_eq u a n h]
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_inter_iff, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by cases hb : ω (childE (⟨(u, a), h⟩ : Echild)) <;> simp_all,
      Classical.not_not.1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1]; simp, fun hh => hh h2⟩

lemma measurableSet_ev (u : V) (a : A) (n : ℕ) : MeasurableSet (Ev u n a) := by
  by_cases hv : u.Valid a
  · rw [ev_valid_eq u a n hv]
    have h1 : MeasurableSet {ω : G.edgeSet → Bool |
        ω (childE (⟨(u, a), hv⟩ : Echild)) = false} :=
      measurableSet_eq_fun (measurable_pi_apply _) measurable_const
    exact h1.union (measurableSet_fwd _ _).compl
  · rw [ev_not_valid u n hv]; exact MeasurableSet.univ

lemma dependsOn_ev (u : V) (a : A) (n : ℕ) : DependsOn (Ev u n a) (Dblk u a) := by
  by_cases hv : u.Valid a
  · rw [ev_valid_eq u a n hv, Dblk, dif_pos hv]
    refine DependsOn.union ?_ ?_
    · have h1 : {ω : G.edgeSet → Bool | ω (childE (⟨(u, a), hv⟩ : Echild)) = false} =
          ({ω | ω (childE (⟨(u, a), hv⟩ : Echild)) = true})ᶜ := by
        ext ω; cases hb : ω (childE (⟨(u, a), hv⟩ : Echild)) <;> simp_all
      rw [h1]
      refine DependsOn.mono (DependsOn.compl (dependsOn_coord (childE (⟨(u, a), hv⟩ : Echild)))) ?_
      intro e he
      rw [Set.mem_singleton_iff] at he
      subst he
      exact Set.mem_union_left _ (Set.mem_singleton _)
    · exact (fwd_dependsOn _ _).compl.mono (Set.subset_union_right)
  · rw [ev_not_valid u n hv, Dblk, dif_neg hv]
    exact DependsOn.univ _

lemma disjoint_Dblk (u : V) : Pairwise (fun a b => Disjoint (Dblk u a) (Dblk u b)) := by
  intro a b hab
  by_cases ha : u.Valid a
  · by_cases hb : u.Valid b
    · simp only [Dblk, dif_pos ha, dif_pos hb, Set.mem_union, Set.mem_singleton_iff]
      refine Set.disjoint_left.2 ?_
      intro e he1 he2
      simp only [Set.mem_union, Set.mem_singleton_iff] at he1 he2
      rcases he1 with h1 | h1
      · rcases he2 with h2 | h2
        · exact hab (by
            have hx : (⟨(u, a), ha⟩ : Echild) = ⟨(u, b), hb⟩ := childE_inj (h1.symm.trans h2)
            simpa using congrArg (fun x : Echild => x.1.2) hx)
        · subst h1
          exact childE_notMem_subE_snoc_of_ne hab ha hb h2
      · rcases he2 with h2 | h2
        · subst h2
          exact childE_notMem_subE_snoc_of_ne hab.symm hb ha h1
        · exact Set.disjoint_left.1 (subE_snoc_disjoint hab ha hb) h1 h2
    · simp only [Dblk, dif_neg hb, Set.disjoint_empty]
  · simp only [Dblk, dif_neg ha, Set.empty_disjoint]

/-- **The branching recursion** for the probability that the forward cluster does not reach
one level deeper. -/
theorem measure_notFwd_succ (r : Fin 2 → unitInterval) (u : V) (n : ℕ) :
    pr r {ω | ¬ Fwd ω u (n + 1)} =
      ∏ a : A, if h : u.Valid a then
        (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n}) else 1 := by
  classical
  have hset : {ω : G.edgeSet → Bool | ¬ Fwd ω u (n + 1)} = ⋂ a, Ev u n a := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ev]
    rw [fwd_succ]
    constructor
    · intro h a h'
      by_cases hb : ω (childE (⟨(u, a), h'⟩ : Echild)) = true
      · exact Or.inr fun hf => h ⟨a, h', hb, hf⟩
      · exact Or.inl (by cases hc : ω (childE (⟨(u, a), h'⟩ : Echild)) <;> simp_all)
    · rintro h ⟨a, h', hb, hf⟩
      rcases h a h' with hc | hc
      · rw [hb] at hc; exact Bool.noConfusion hc
      · exact hc hf
  have hprod := measure_iInter_eq_prod
    (m := fun e : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf e))))
    (fun a => Ev u n a) (fun a => Dblk u a) (disjoint_Dblk u)
    (fun a => measurableSet_ev u a n) (fun a => dependsOn_ev u a n)
  rw [hset]
  show (law r).real (⋂ a, Ev u n a) = _
  rw [measureReal_def, hprod, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  show ((law r) (Ev u n a)).toReal = _
  rw [← measureReal_def]
  by_cases hv : u.Valid a
  · rw [dif_pos hv]
    have hdis : Disjoint ({childE (⟨(u, a), hv⟩ : Echild)} : Set G.edgeSet)
        (subE (u.snoc a hv)) := by
      rw [Set.disjoint_left]
      intro e he1 he2
      simp only [Set.mem_singleton_iff] at he1
      subst he1
      exact childE_notMem_subE_snoc hv he2
    have h1 : pr r ({ω : G.edgeSet → Bool |
        ω (childE (⟨(u, a), hv⟩ : Echild)) = true} ∩ {ω | Fwd ω (u.snoc a hv) n}) =
        pr r {ω : G.edgeSet → Bool | ω (childE (⟨(u, a), hv⟩ : Echild)) = true} *
          pr r {ω | Fwd ω (u.snoc a hv) n} :=
      pr_inter r (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
        (measurableSet_fwd _ _) (dependsOn_coord _) (fwd_dependsOn _ _) hdis
    have hinter : (law r).real ({ω : G.edgeSet → Bool |
        ω (childE (⟨(u, a), hv⟩ : Echild)) = true} ∩ {ω | Fwd ω (u.snoc a hv) n}) =
        (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a hv) n} := by
      refine h1.trans ?_
      rw [pr_coord, letterOf_childE]
    have hadd : (law r).real (Ev u n a) + (r (acls a) : ℝ) *
        pr r {ω | Fwd ω (u.snoc a hv) n} = 1 := by
      have h1 := measureReal_add_measureReal_compl (μ := law r) (s := Ev u n a)
        (measurableSet_ev u a n)
      rw [ev_compl_eq u a n hv, hinter] at h1
      simpa using h1
    linarith
  · rw [dif_neg hv, ev_not_valid u n hv, measureReal_def, measure_univ, ENNReal.toReal_one]

end Ultra
