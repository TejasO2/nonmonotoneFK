import FK.AGTree.Criterion

/-!
# The strict phase comparison on the two-class tree
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal unitInterval Topology

lemma pr_compl_eq (r : Fin 2 → unitInterval) (A : Set (G.edgeSet → Bool))
    (hA : MeasurableSet A) : pr r Aᶜ = 1 - pr r A := by
  have h := measureReal_add_measureReal_compl (μ := law r) (s := A) hA
  have h1 : (law r).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [h1] at h
  linarith [h]

lemma card_valid_root_total : (Finset.univ.filter (fun a : A => V.root.Valid a)).card = 5 := by
  decide

lemma card_univ_A : Fintype.card A = 5 := by
  simp [A]

lemma root_valid (a : A) : V.root.Valid a := Or.inl rfl

lemma card_valid_ge_four {v : V} (hv : v.w ≠ []) :
    4 ≤ (Finset.univ.filter (fun a : A => v.Valid a)).card := by
  have hsub : (Finset.univ.filter (fun a : A => ¬ v.Valid a)) ⊆ {v.w.getLast hv} := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at ha ⊢
    rw [V.Valid] at ha
    by_contra hne
    exact ha (Or.inr (by
      rw [List.getLast?_eq_some_getLast hv]
      exact fun he => hne (by simpa using he.symm)))
  have h1 : (Finset.univ.filter (fun a : A => ¬ v.Valid a)).card ≤ 1 := by
    have hle := Finset.card_le_card hsub
    simpa using hle
  have h2 : (Finset.univ.filter (fun a : A => v.Valid a)).card +
      (Finset.univ.filter (fun a : A => ¬ v.Valid a)).card = 5 := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [card_univ_A]
  omega

lemma snoc_last (v : V) (a : A) (h : v.Valid a) :
    (v.snoc a h).w.getLast (by simp) = a := by
  simp

lemma prod_ite_pow {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (c : ℝ) :
    ∏ a : ι, (if p a then c else 1) = c ^ (Finset.univ.filter p).card := by
  rw [← Finset.prod_filter]
  simp

lemma prod_le_prod_real {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine mul_le_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (le_trans (hf a (Finset.mem_insert_self a s)) (h a (Finset.mem_insert_self a s)))

lemma step_nonneg (r : Fin 2 → unitInterval) {P : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (a : A) :
    0 ≤ 1 - (r (acls a) : ℝ) * P := by
  have hr0 : (0:ℝ) ≤ (r (acls a) : ℝ) := unitInterval.nonneg _
  have hr1 : (r (acls a) : ℝ) ≤ 1 := unitInterval.le_one _
  nlinarith

lemma step_le (r : Fin 2 → unitInterval) (w : Fin 2 → ℝ) (c : ℝ)
    (hfac : ∀ a : A, (1 - (r (acls a) : ℝ)) + (r (acls a) : ℝ) * w (acls a) ≤ c)
    (a : A) {P : ℝ} (hP : 1 - w (acls a) ≤ P) :
    1 - (r (acls a) : ℝ) * P ≤ c := by
  have hr0 : (0:ℝ) ≤ (r (acls a) : ℝ) := unitInterval.nonneg _
  have h1 : (r (acls a) : ℝ) * (1 - w (acls a)) ≤ (r (acls a) : ℝ) * P :=
    mul_le_mul_of_nonneg_left hP hr0
  have h3 : 1 - (r (acls a) : ℝ) * (1 - w (acls a)) =
      (1 - (r (acls a) : ℝ)) + (r (acls a) : ℝ) * w (acls a) := by ring
  linarith [hfac a]

lemma if_step_nonneg (r : Fin 2 → unitInterval) (u : V) (a : A) (n : ℕ) :
    0 ≤ (if h : u.Valid a then
      (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n}) else 1) := by
  by_cases h : u.Valid a
  · rw [dif_pos h]; exact step_nonneg r (pr_nonneg r _) (pr_le_one r _) a
  · rw [dif_neg h]; exact zero_le_one

lemma if_step_le (r : Fin 2 → unitInterval) (w : Fin 2 → ℝ) (c : ℝ)
    (hfac : ∀ a : A, (1 - (r (acls a) : ℝ)) + (r (acls a) : ℝ) * w (acls a) ≤ c)
    (u : V) (a : A) (n : ℕ)
    (hP : ∀ (h : u.Valid a), 1 - w (acls a) ≤ pr r {ω | Fwd ω (u.snoc a h) n}) :
    (if h : u.Valid a then
      (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n}) else 1) ≤
      (if h : u.Valid a then c else 1) := by
  by_cases h : u.Valid a
  · rw [dif_pos h, dif_pos h]
    exact step_le r w c hfac a (hP h)
  · rw [dif_neg h, dif_neg h]

/-- **Percolation criterion.** A uniform factor bound `c < 1` with `c^4 ≤ w ≤ 1`
forces percolation of the root cluster. -/
theorem cluster_pos_of_uniform (r : Fin 2 → unitInterval) (w : Fin 2 → ℝ) (c : ℝ)
    (hw1 : ∀ i, w i < 1) (hw0 : ∀ i, 0 ≤ w i) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hfac : ∀ a : A, (1 - (r (acls a) : ℝ)) + (r (acls a) : ℝ) * w (acls a) ≤ c)
    (h4 : ∀ i, c ^ 4 ≤ w i) (h5 : c ^ 5 < 1) :
    0 < pr r {ω | Cluster ω V.root} := by
  classical
  have key : ∀ n : ℕ,
      (∀ v : V, (h : v.w ≠ []) → 1 - pr r {ω | Fwd ω v n} ≤ w (acls (v.w.getLast h))) ∧
      (1 - pr r {ω | Fwd ω V.root n} ≤ c ^ 5) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [pr_fwd_zero]; linarith [hw0 (acls (v.w.getLast hv))]
      · rw [pr_fwd_zero]; linarith [pow_nonneg hc0 5]
    | succ n ih =>
      have hstep := fun (u : V) => measure_notFwd_succ r u n
      have hcompl : ∀ (u : V), (1:ℝ) - pr r {ω : G.edgeSet → Bool | Fwd ω u (n + 1)} =
          pr r {ω : G.edgeSet → Bool | ¬ Fwd ω u (n + 1)} := by
        intro u
        rw [← pr_compl_eq r {ω : G.edgeSet → Bool | Fwd ω u (n + 1)}
          (measurableSet_fwd u (n + 1))]
        rfl
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [hcompl v, hstep v]
        have hle := prod_le_prod_real Finset.univ
          (f := fun a : A => if h : v.Valid a then
            (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (v.snoc a h) n}) else 1)
          (g := fun a : A => if h : v.Valid a then c else 1)
          (fun a _ => if_step_nonneg r v a n)
          (fun a _ => if_step_le r w c hfac v a n (fun h => by
            have hc := ih.1 (v.snoc a h) (by simp)
            rw [show acls ((v.snoc a h).w.getLast (by simp)) = acls a from by
              rw [snoc_last]] at hc
            linarith))
        refine le_trans hle ?_
        have hpow : (∏ a : A, (if h : v.Valid a then c else 1)) =
            c ^ (Finset.univ.filter (fun a : A => v.Valid a)).card := prod_ite_pow _ c
        rw [hpow]
        exact le_trans (pow_le_pow_of_le_one hc0 hc1 (card_valid_ge_four hv)) (h4 _)
      · rw [hcompl V.root, hstep V.root]
        have hle := prod_le_prod_real Finset.univ
          (f := fun a : A => if h : V.root.Valid a then
            (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (V.root.snoc a h) n}) else 1)
          (g := fun _ : A => c)
          (fun a _ => if_step_nonneg r V.root a n)
          (fun a _ => by
            have h2 : (if h : V.root.Valid a then
                (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (V.root.snoc a h) n}) else 1) ≤
                (if h : V.root.Valid a then c else 1) :=
              if_step_le r w c hfac V.root a n (fun h => by
                have hc := ih.1 (V.root.snoc a h) (by simp)
                rw [show acls ((V.root.snoc a h).w.getLast (by simp)) = acls a from by
                  rw [snoc_last]] at hc
                linarith)
            rwa [dif_pos (root_valid a)] at h2)
        refine le_trans hle ?_
        rw [Finset.prod_const, Finset.card_univ, card_univ_A]
  have htend := pr_cluster_tendsto r V.root
  have hlim : 1 - c ^ 5 ≤ pr r {ω | Cluster ω V.root} := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
    filter_upwards with k
    have := (key k).2
    linarith
  linarith

end Ultra
