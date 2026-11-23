import FK.CanonicalDynamics

/-!
# Finite enhanced comparison for `1 < q`

This is the `q > 1` case of the deduction of Theorem 1.2 from Propositions
3.1 and 3.2.  Both enhancement sets and a strict witness are constructed. The
uniform clocks and auxiliary schedules are proved canonically and are not
inputs.  The mixed-parameter convention below is `p' = FK.prime q p < p`;
hence the closed cutset improves the upper bound and the open path improves the
lower bound, as in the paper.
-/

namespace FK.EnhancedComparisons

open Set
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.WiredEnhancement
open OpenPath
open FKEnhancement

noncomputable section

open scoped Classical BigOperators

/-- **Theorem 1.2 for `1 < q`, actual finite wired labelled multigraphs.**
There are nonempty closed-cutset and open-path enhanced sets, each with a
strictly positive local enhancement at one of its edges. -/
theorem theorem_1_2_of_one_lt_q
    (G : LabelledMultigraph) {q p : NNReal}
    (hq1 : 1 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition)
    (hconn : WiredConnected G ξ) (htwo : TwoWiredVertices G ξ)
    (hnotforest : ¬ IsWiredForest G ξ) :
    ∃ Ec : Set G.Edge, Ec.Nonempty ∧
      (∃ e ∈ Ec, 0 < extendedCutsetEpsilon G ξ Ec
        (actualLowerParameter p hp1.le)
        (actualPrimeParameter (lt_trans zero_lt_one hq1 : 0 < q) hp1.le) e) ∧
      StochasticallyDominates (G.fkMeasure (lt_trans zero_lt_one hq1) hp1.le ξ)
        (upperEnhancedLaw (graphConnectionEvent G ξ) Ec
          (actualPrime_le_lower (lt_trans zero_lt_one hq1 : 0 < q) hp0 hp1 hq1)) ∧
      ∃ Ep : Finset G.Edge, ∃ Γ : G.Edge → Set (Finset G.Edge),
        Ep.Nonempty ∧ HasEnhancingPaths Ep Γ ∧
        (∀ e ∈ Ep, ∀ {ω : OpenPath.Config G.Edge}, OpenPath.SomePathOpen (Γ e) ω →
          FK.Finite.Conditional.endpointsConnectedWithout G ξ e (OpenPath.configToBool ω)) ∧
        (∃ e ∈ Ep, 0 < OpenPath.lowerEpsilon Ep (p : ℝ)
          (FK.prime (q : ℝ) (p : ℝ))
          (FK.prime_mem_Icc (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
            (by exact_mod_cast hp0.le) (by exact_mod_cast hp1.le)) Γ e) ∧
        FKEnhancement.StochasticallyDominates
          ((OpenPath.lowerProductPMF Ep (by exact_mod_cast hp1.le)
            (FK.prime_mem_Icc (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
              (by exact_mod_cast hp0.le) (by exact_mod_cast hp1.le))
            (FK.Finite.WiredEnhancement.prime_lt_of_one_lt_q
              (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
              (by exact_mod_cast hp0) (by exact_mod_cast hp1)
              (by exact_mod_cast hq1)).le Γ).map OpenPath.configToBool).toMeasure
            (G.fkPMF (lt_trans zero_lt_one hq1) hp1.le ξ).toMeasure := by
  have hq : 0 < q := lt_trans zero_lt_one hq1
  obtain ⟨Ec, hEc, hεmem, ec, hec, hεpos, χ, hχ⟩ :=
    exists_pos_cutsetEpsilon_fk G ξ hconn htwo (q := (q : ℝ)) (p := (p : ℝ))
      (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq1.ne')
  have hnforest := hnotforest
  rw [IsWiredForest] at hnforest
  push Not at hnforest
  obtain ⟨e, he⟩ := hnforest
  obtain ⟨γ, heγ, hγ⟩ := exists_routeCertificate_of_reachable G ξ e he
  let Γ := wiredPathCollection G e γ
  have hΓ : HasEnhancingPaths {e} Γ := hasEnhancingPaths_wiredPath G heγ
  have hpath : ∀ f ∈ ({e} : Finset G.Edge), ∀ {ω : Config G.Edge},
      SomePathOpen (Γ f) ω → FK.Finite.Conditional.endpointsConnectedWithout G ξ f (OpenPath.configToBool ω) := by
    intro f hf
    have hfe : f = e := Finset.mem_singleton.mp hf
    subst f
    intro ω hω
    obtain ⟨δ, hδ, hδopen⟩ := hω
    have hδeq : δ = γ := by simpa [Γ, wiredPathCollection] using hδ
    subst δ
    apply hγ (OpenPath.configToBool ω)
    intro a ha
    exact (FK.Finite.WiredEnhancement.configToBool_eq_true ω a).mpr (hδopen a ha)
  have hp'0 : 0 < FK.prime (q : ℝ) (p : ℝ) :=
    FK.prime_pos (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1.le)
  have hp'1 : FK.prime (q : ℝ) (p : ℝ) < 1 :=
    prime_lt_one_interior (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hlt : FK.prime (q : ℝ) (p : ℝ) < (p : ℝ) :=
    prime_lt_of_one_lt_q (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq1)
  have hp_pos : 0 < lowerEpsilon {e} (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
      (FK.prime_mem_Icc (by exact_mod_cast hq) (by exact_mod_cast hp0.le)
        (by exact_mod_cast hp1.le)) Γ e :=
    lowerEpsilon_pos hΓ (FK.prime_mem_Icc (by exact_mod_cast hq)
      (by exact_mod_cast hp0.le) (by exact_mod_cast hp1.le)) hp'0 hp'1 hlt
      (Finset.mem_singleton_self e)
  have hne : Nonempty G.Edge := ⟨ec⟩
  have hupper := graphConnectionEvent_upper_comparison_canonical G hq hp0 hp1 hq1 ξ Ec hne
  have hlower := OpenPath.LowerPathCoupling.lower_path_comparison_of_one_lt_q_canonical
    G hq1 hp0 hp1 ξ {e} Γ hΓ hpath hne
  refine ⟨Ec, hEc, ?_, hupper, {e}, Γ, ⟨e, Finset.mem_singleton_self e⟩,
    hΓ, hpath, ⟨e, Finset.mem_singleton_self e, hp_pos⟩, hlower⟩
  refine ⟨ec, hec, ?_⟩
  change 0 < extendedCutsetEpsilon G ξ Ec
    (unitParameter (p : ℝ) hp0.le hp1.le)
    (unitParameter (FK.prime (q : ℝ) (p : ℝ)) hp'0.le hp'1.le) ec
  exact hεpos

end

end FK.EnhancedComparisons
