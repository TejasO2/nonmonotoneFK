import FK.AdaptiveGood

/-! # Singleton conditionals of an independent product on a sum of edge types -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.FinitePlane
open FK.Finite.MarkovFactorization
open FK.Exploration.FKCoupling

/-- The ordinary sum-of-functions configuration equivalence. -/
def sumConfigEquiv {A B : Type*} : (A ⊕ B → Bool) ≃ (A → Bool) × (B → Bool) :=
  Equiv.sumArrowEquivProdArrow A B Bool

/-- Join two configurations without passing through a graph alias. -/
def joinSum {A B : Type*} (ω : A → Bool) (η : B → Bool) : A ⊕ B → Bool :=
  Sum.elim ω η

/-- Independent product on the sum-labelled configuration space. -/
noncomputable def productJoinLaw {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration) : PMF (G.Edge ⊕ H.Edge → Bool) :=
  (independentProd μ ν).map (sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm

lemma ofPMF_productJoinLaw_apply {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration)
    (ω : G.Configuration) (η : H.Configuration) :
    (Glauber.ofPMF (productJoinLaw μ ν)).mass (joinSum ω η) =
      (Glauber.ofPMF μ).mass ω * (Glauber.ofPMF ν).mass η := by
  simp only [productJoinLaw, Glauber.ofPMF_mass]
  change ((independentProd μ ν).map (sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm
    ((sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm (ω, η))).toReal = _
  have hmap := pmf_map_equiv_apply
    (d := (sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm) (independentProd μ ν)
    ((sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm (ω, η))
  rw [hmap]
  simp

lemma productJoinLaw_ne_zero {G H : LabelledMultigraph}
    {μ : PMF G.Configuration} {ν : PMF H.Configuration}
    (hμ : ∀ ω, μ ω ≠ 0) (hν : ∀ η, ν η ≠ 0) :
    ∀ ρ, productJoinLaw μ ν ρ ≠ 0 := by
  intro ρ
  rw [productJoinLaw]
  let z := sumConfigEquiv (A := G.Edge) (B := H.Edge) ρ
  have heq : ρ = (sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm z := by simp [z]
  rw [heq]
  have hmap := pmf_map_equiv_apply (d := (sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm)
    (independentProd μ ν) ((sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm z)
  rw [hmap]
  exact mul_ne_zero (hμ _) (hν _)

/-- The left off-edge part of a sum off-edge configuration. -/
def leftOff {G H : LabelledMultigraph} (a : G.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inl a)) :
    Glauber.OffConfig Bool G.Edge a :=
  fun x => off ⟨Sum.inl x.1, by
    intro h
    exact x.2 (Sum.inl.inj h)⟩

/-- The full right configuration revealed by a left off-edge configuration. -/
def rightFull {G H : LabelledMultigraph} (a : G.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inl a)) : H.Configuration :=
  fun b => off ⟨Sum.inr b, by intro h; cases h⟩

/-- The right off-edge part of a sum off-edge configuration. -/
def rightOff {G H : LabelledMultigraph} (b : H.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inr b)) :
    Glauber.OffConfig Bool H.Edge b :=
  fun x => off ⟨Sum.inr x.1, by
    intro h
    exact x.2 (Sum.inr.inj h)⟩

/-- The full left configuration revealed by a right off-edge configuration. -/
def leftFull {G H : LabelledMultigraph} (b : H.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inr b)) : G.Configuration :=
  fun a => off ⟨Sum.inl a, by intro h; cases h⟩

lemma configSplit_join_left {G H : LabelledMultigraph} (a : G.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inl a)) (b : Bool) :
    (Glauber.configSplit Bool (Sum.inl a)).symm (off, b) =
      joinSum ((Glauber.configSplit Bool a).symm (leftOff a off, b)) (rightFull a off) := by
  funext e
  cases e with
  | inl x =>
      by_cases hx : x = a
      · subst x
        simp [joinSum, Glauber.configSplit, Equiv.funSplitAt_symm_apply]
      · simp [joinSum, Glauber.configSplit, Equiv.funSplitAt_symm_apply, leftOff, hx]
  | inr y => rfl

lemma configSplit_join_right {G H : LabelledMultigraph} (b : H.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inr b)) (c : Bool) :
    (Glauber.configSplit Bool (Sum.inr b)).symm (off, c) =
      joinSum (leftFull b off) ((Glauber.configSplit Bool b).symm (rightOff b off, c)) := by
  funext e
  cases e with
  | inl x => rfl
  | inr y =>
      by_cases hy : y = b
      · subst y
        simp [joinSum, Glauber.configSplit, Equiv.funSplitAt_symm_apply]
      · simp [joinSum, Glauber.configSplit, Equiv.funSplitAt_symm_apply, rightOff, hy]

lemma outside_productJoinLaw_left {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration) (a : G.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inl a)) :
    Glauber.outsideMassConj (Glauber.configSplit Bool (Sum.inl a))
      (Glauber.ofPMF (productJoinLaw μ ν)) off =
      Glauber.outsideMassConj (Glauber.configSplit Bool a) (Glauber.ofPMF μ)
        (leftOff a off) * (Glauber.ofPMF ν).mass (rightFull a off) := by
  unfold Glauber.outsideMassConj
  simp_rw [configSplit_join_left, ofPMF_productJoinLaw_apply]
  rw [Finset.sum_mul]

lemma outside_productJoinLaw_right {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration) (b : H.Edge)
    (off : Glauber.OffConfig Bool (G.Edge ⊕ H.Edge) (Sum.inr b)) :
    Glauber.outsideMassConj (Glauber.configSplit Bool (Sum.inr b))
      (Glauber.ofPMF (productJoinLaw μ ν)) off =
      (Glauber.ofPMF μ).mass (leftFull b off) *
        Glauber.outsideMassConj (Glauber.configSplit Bool b) (Glauber.ofPMF ν)
          (rightOff b off) := by
  unfold Glauber.outsideMassConj
  simp_rw [configSplit_join_right, ofPMF_productJoinLaw_apply]
  rw [Finset.mul_sum]

/-- Singleton conditionals of a product, with the known conditional on the
active side and its companion configuration held fixed. -/
noncomputable def productConditionals {G H : LabelledMultigraph}
    (cL : Glauber.EdgeConditionals Bool G.Edge)
    (cR : Glauber.EdgeConditionals Bool H.Edge) :
    Glauber.EdgeConditionals Bool (G.Edge ⊕ H.Edge)
  | Sum.inl a, off => cL a (leftOff a off)
  | Sum.inr b, off => cR b (rightOff b off)

lemma productJoinLaw_hasEdgeConditional_left {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration)
    {cL : Glauber.EdgeConditionals Bool G.Edge}
    (cR : Glauber.EdgeConditionals Bool H.Edge)
    (hc : ∀ e, Glauber.HasEdgeConditional (Glauber.ofPMF μ) cL e)
    (a : G.Edge) :
    Glauber.HasEdgeConditional (Glauber.ofPMF (productJoinLaw μ ν))
      (productConditionals cL cR) (Sum.inl a) := by
  intro off b
  rw [show (productConditionals cL cR (Sum.inl a) off).mass b =
      (cL a (leftOff a off)).mass b from rfl]
  rw [configSplit_join_left, ofPMF_productJoinLaw_apply, outside_productJoinLaw_left]
  rw [(hc a) (leftOff a off) b]
  ring

lemma productJoinLaw_hasEdgeConditional_right {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration)
    (cL : Glauber.EdgeConditionals Bool G.Edge)
    {cR : Glauber.EdgeConditionals Bool H.Edge}
    (hc : ∀ e, Glauber.HasEdgeConditional (Glauber.ofPMF ν) cR e)
    (b : H.Edge) :
    Glauber.HasEdgeConditional (Glauber.ofPMF (productJoinLaw μ ν))
      (productConditionals cL cR) (Sum.inr b) := by
  intro off c
  rw [show (productConditionals cL cR (Sum.inr b) off).mass c =
      (cR b (rightOff b off)).mass c from rfl]
  rw [configSplit_join_right, ofPMF_productJoinLaw_apply, outside_productJoinLaw_right]
  rw [(hc b) (rightOff b off) c]
  ring

lemma productJoinLaw_hasEdgeConditional {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration)
    {cL : Glauber.EdgeConditionals Bool G.Edge}
    {cR : Glauber.EdgeConditionals Bool H.Edge}
    (hcL : ∀ e, Glauber.HasEdgeConditional (Glauber.ofPMF μ) cL e)
    (hcR : ∀ e, Glauber.HasEdgeConditional (Glauber.ofPMF ν) cR e)
    (e : G.Edge ⊕ H.Edge) :
    Glauber.HasEdgeConditional (Glauber.ofPMF (productJoinLaw μ ν))
      (productConditionals cL cR) e := by
  cases e with
  | inl a => exact productJoinLaw_hasEdgeConditional_left μ ν cR hcL a
  | inr b => exact productJoinLaw_hasEdgeConditional_right μ ν cL hcR b

/-- The nested FK–Bernoulli product obeys the same uniform upper conditional
bound on every arbitrary revealed history. -/
theorem productJoinLaw_fk_bernoulli_bit_le {G H : LabelledMultigraph}
    (τ : G.BoundaryPartition) (ξO : H.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    {h : Assignment (G.Edge ⊕ H.Edge)} {e : G.Edge ⊕ H.Edge} (he : h e = none) :
    (bit (productJoinLaw (G.fkPMF hq hp₁.le τ)
      (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
      (productJoinLaw_ne_zero
        (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ τ ω)
        (bernoulliProductPMF_ne_zero H ξO (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁))) h e true).toReal ≤
      (upperRateNN q p : ℝ) := by
  let cL := fkConditionals G hq hp₁.le τ
  let cR : Glauber.EdgeConditionals Bool H.Edge := fun _ _ =>
    boolLaw (upperRateNN q p : ℝ) ⟨upperRateNN_pos hp₀ |>.le, upperRateNN_lt_one hq hp₀ hp₁ |>.le⟩
  have hcL : ∀ a, Glauber.HasEdgeConditional (Glauber.ofPMF (G.fkPMF hq hp₁.le τ)) cL a :=
    fun a => fk_hasEdgeConditional G hq hp₁.le τ a
  have hcR : ∀ b, Glauber.HasEdgeConditional
      (Glauber.ofPMF (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)) cR b := by
    intro b
    rw [H.ofPMF_bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le]
    exact boolProduct_hasEdgeConditional (fun _ : H.Edge => (upperRateNN q p : ℝ))
      (fun _ => ⟨(upperRateNN_pos hp₀).le, (upperRateNN_lt_one hq hp₀ hp₁).le⟩) b
  have hb := bit_true_toReal_le_of_bound
    (productJoinLaw (G.fkPMF hq hp₁.le τ)
      (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
    (productJoinLaw_ne_zero
      (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ τ ω)
      (bernoulliProductPMF_ne_zero H ξO (upperRateNN_pos hp₀)
        (upperRateNN_lt_one hq hp₀ hp₁))) he
    (productConditionals cL cR)
    (productJoinLaw_hasEdgeConditional _ _ hcL hcR e)
    (fkHi q p) (by
      intro off
      cases e with
      | inl a => exact fkRate_le_max G τ a (leftOff a off)
      | inr b =>
          rw [show (productConditionals cL cR (Sum.inr b) off).mass true =
            (upperRateNN q p : ℝ) from
              boolLaw_true _ ⟨(upperRateNN_pos hp₀).le, (upperRateNN_lt_one hq hp₀ hp₁).le⟩]
          exact (coe_upperRateNN q p hq hp₁.le).le)
  simpa [coe_upperRateNN q p hq hp₁.le] using hb

end FK.Adaptive
