import FK.CanonicalDynamics

/-!
# Finite enhanced comparison for `q < 1`

The lower bound is improved by a closed cutset and the upper bound by an open
path. This is the `q < 1` case of the deduction of Theorem 1.2 from
Propositions 3.1 and 3.2 for actual finite wired labelled multigraphs.
-/

namespace FK.EnhancedComparisons

open Set
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.WiredEnhancement
open OpenPath
open FKEnhancement

noncomputable section

open scoped Classical BigOperators

/-- **Theorem 1.2 for `q < 1`, actual finite wired labelled multigraphs.**
Strict local enhancements are constructed in both directions, including the
actual graph semantics of every enhanced path certificate. -/
theorem theorem_1_2_of_lt_one
    (G : LabelledMultigraph) {q p : NNReal}
    (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition)
    (hconn : WiredConnected G ξ) (htwo : TwoWiredVertices G ξ)
    (hnotforest : ¬ IsWiredForest G ξ) :
    ∃ Ec : Set G.Edge, Ec.Nonempty ∧
      (∃ e ∈ Ec, 0 < extendedCutsetEpsilon G ξ Ec
        (actualLowerParameter p hp1.le)
        (actualPrimeParameter hq0 hp1.le) e) ∧
      StochasticallyDominates
        (lowerEnhancedLaw (graphConnectionEvent G ξ) Ec
          (actualLower_le_prime hq0 hp0 hp1 hq1))
        (G.fkMeasure hq0 hp1.le ξ) ∧
      ∃ Ep : Finset G.Edge, ∃ Γ : G.Edge → Set (Finset G.Edge),
        Ep.Nonempty ∧ HasEnhancingPaths Ep Γ ∧
        (∀ e ∈ Ep, ∀ {ω : OpenPath.Config G.Edge}, OpenPath.SomePathOpen (Γ e) ω →
          FK.Finite.Conditional.endpointsConnectedWithout G ξ e (OpenPath.configToBool ω)) ∧
        (∃ e ∈ Ep, 0 < OpenPath.upperEpsilon Ep (p : ℝ)
          (FK.prime (q : ℝ) (p : ℝ))
          ⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩ Γ e) ∧
        FKEnhancement.StochasticallyDominates
          (G.fkPMF hq0 hp1.le ξ).toMeasure
          ((OpenPath.upperProductPMF Ep ⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩
            (FK.Finite.WiredEnhancement.prime_lt_one_interior
              (by exact_mod_cast hq0)
              (by exact_mod_cast hp0) (by exact_mod_cast hp1)).le
            (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
              (by exact_mod_cast hq0)
              (by exact_mod_cast hp0) (by exact_mod_cast hp1)
              (by exact_mod_cast hq1)).le Γ).map OpenPath.configToBool).toMeasure := by
  have hq : 0 < q := hq0
  obtain ⟨Ec, hEc, hεmem, ec, hec, hεpos, χ, hχ⟩ :=
    exists_pos_cutsetEpsilon_fk G ξ hconn htwo (q := (q : ℝ)) (p := (p : ℝ))
      (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq1.ne)
  have hnforest := hnotforest
  rw [IsWiredForest] at hnforest
  push Not at hnforest
  obtain ⟨e, he⟩ := hnforest
  obtain ⟨γ, heγ, hγ⟩ := exists_routeCertificate_of_reachable G ξ e he
  let Γ := wiredPathCollection G e γ
  have hΓ : HasEnhancingPaths {e} Γ := hasEnhancingPaths_wiredPath G heγ
  have hpath : ∀ f ∈ ({e} : Finset G.Edge), ∀ {ω : Config G.Edge},
      SomePathOpen (Γ f) ω → FK.Finite.Conditional.endpointsConnectedWithout G ξ f
        (OpenPath.configToBool ω) := by
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
  have hlt : (p : ℝ) < FK.prime (q : ℝ) (p : ℝ) :=
    lt_prime_of_q_lt_one (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq1)
  have hp_pos : 0 < upperEpsilon {e} (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
      ⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩ Γ e :=
    upperEpsilon_pos hΓ ⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩
      (by exact_mod_cast hp0) (by exact_mod_cast hp1) hlt (Finset.mem_singleton_self e)
  have hne : Nonempty G.Edge := ⟨ec⟩
  have hlower := graphConnectionEvent_lower_comparison_canonical G hq hp0 hp1 hq1 ξ Ec hne
  have hupper := CanonicalDynamics.graphConnectionEvent_upper_path_comparison_canonical
    G hq hp0 hp1 hq1 ξ {e} Γ (fun f hf => hΓ.auxiliary f hf)
    (by
      intro f hf
      unfold graphConnectionEvent
      exact hpath f hf) hne
  refine ⟨Ec, hEc, ?_, hlower, {e}, Γ, ⟨e, Finset.mem_singleton_self e⟩,
    hΓ, hpath, ⟨e, Finset.mem_singleton_self e, hp_pos⟩, hupper⟩
  refine ⟨ec, hec, ?_⟩
  change 0 < extendedCutsetEpsilon G ξ Ec
    (unitParameter (p : ℝ) hp0.le hp1.le)
    (unitParameter (FK.prime (q : ℝ) (p : ℝ)) hp'0.le hp'1.le) ec
  exact hεpos

end

end FK.EnhancedComparisons
