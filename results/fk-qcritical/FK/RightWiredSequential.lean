import FK.WiredMaximalStrata

/-!
# Explicit configuration-level right-wired sequential triples

The three-history process is decoded after `k + m` bits.  It has two actual
right-wired FK marginals and an actual Bernoulli-product upper marginal on the
same finite edge labels, with pointwise support order to the upper coordinate.
-/

namespace FK.Exploration.RightWiredSequential

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior FK.Exploration.WiredMaximalStrata

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- The actual lower FK law on transported finite labels with right-supported
wiring pulled back from the original sum-labelled graph. -/
noncomputable def rightWiredLaw
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₁ : p < 1) (ζ : Setoid K) :
    PMF (Fin (k + m) → Bool) :=
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let T := transportedAmbient si ti so xo
  let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
    (rightWiredBoundary si ti so xo ζ)
  T.fkPMF hq hp₁.le ξ

lemma rightWiredLaw_ne_zero
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (ω : Fin (k + m) → Bool) :
    rightWiredLaw si ti so xo hq hp₁ ζ ω ≠ 0 := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let T := transportedAmbient si ti so xo
  let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
    (rightWiredBoundary si ti so xo ζ)
  exact fkPMF_ne_zero T hq hp₀ hp₁ ξ ω

lemma rightWiredLaw_nextBound
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (x : List Bool) :
    (canonicalNext (rightWiredLaw si ti so xo hq hp₁ ζ)
      (rightWiredLaw_ne_zero si ti so xo hq hp₀ hp₁ ζ) x true).toReal ≤
        (upperRateNN q p : ℝ) := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let T := transportedAmbient si ti so xo
  let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
    (rightWiredBoundary si ti so xo ζ)
  exact fk_upper_nextBound _ _ ξ hq hp₀ hp₁ x

/-- Pushforward back to the original sum-labelled graph is the actual FK law
with the corresponding free-left/right-supported boundary setoid. -/
theorem map_toAmbient_rightWiredLaw
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    (rightWiredLaw si ti so xo hq hp₁ ζ).map (toAmbientConfig si ti so xo) =
      G.fkPMF hq hp₁.le (rightWiredBoundary si ti so xo ζ) := by
  intro G
  exact G.map_transport_fkPMF (Equiv.refl (U ⊕ K)) exteriorFirst
    (rightWiredBoundary si ti so xo ζ) hq hp₀ hp₁

/-- A one-bit lower/upper process for either right-wired law. -/
noncomputable def rightWiredUpperStep
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ζ : Setoid K) :=
  orderedUpperStep (rightWiredLaw si ti so xo hq hp₁ ζ)
    (rightWiredLaw_ne_zero si ti so xo hq hp₀ hp₁ ζ) (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le)
    (rightWiredLaw_nextBound si ti so xo hq hp₀ hp₁ ζ)

/-- A one-bit process for two right-wired coordinates and one common upper
coordinate. -/
noncomputable def rightWiredTripleStep
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) :=
  gluedUpperStep (rightWiredLaw si ti so xo hq hp₁ ζ₁)
    (rightWiredLaw si ti so xo hq hp₁ ζ₂)
    (rightWiredLaw_ne_zero si ti so xo hq hp₀ hp₁ ζ₁)
    (rightWiredLaw_ne_zero si ti so xo hq hp₀ hp₁ ζ₂)
    (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
    (rightWiredLaw_nextBound si ti so xo hq hp₀ hp₁ ζ₁)
    (rightWiredLaw_nextBound si ti so xo hq hp₀ hp₁ ζ₂)

lemma rightWiredTripleStep_map_fst
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (x₁ x₂ y : List Bool) :
    (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y).map
      (fun z => (z.1, z.2.2)) =
        rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₁ x₁ y := by
  exact gluedUpperStep_map_fst_thd _ _ _ _ _ _ _ _ _ _ _

lemma rightWiredTripleStep_map_snd
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (x₁ x₂ y : List Bool) :
    (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y).map
      (fun z => (z.2.1, z.2.2)) =
        rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₂ x₂ y := by
  exact gluedUpperStep_map_snd_thd _ _ _ _ _ _ _ _ _ _ _

/-- Decode full histories on the transported finite-labelled configurations. -/
def decodeTriple
    {m k : ℕ} (z : List Bool × List Bool × List Bool) :
    (Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool) :=
  (toConfig (k + m) z.1, toConfig (k + m) z.2.1, toConfig (k + m) z.2.2)

/-- The explicit full configuration-level triple. -/
noncomputable def rightWiredTriple
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) :
    PMF ((Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool)) :=
  (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
    [] [] [] (k + m)).map decodeTriple

/-- The first FK marginal is exact. -/
theorem rightWiredTriple_map_fst
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) :
    (rightWiredTriple si ti so xo hq hp₀ hp₁ ζ₁ ζ₂).map (fun z => z.1) =
      rightWiredLaw si ti so xo hq hp₁ ζ₁ := by
  unfold rightWiredTriple
  rw [PMF.map_comp]
  rw [show (fun z : (Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool) => z.1) ∘
      decodeTriple = (fun z : List Bool × List Bool => toConfig (k + m) z.1) ∘
        (fun z : List Bool × List Bool × List Bool => (z.1, z.2.2)) from rfl]
  rw [← PMF.map_comp]
  change (((extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
    [] [] [] (k + m)).map (fun z => (z.1, z.2.2))).map
      (fun z : List Bool × List Bool => toConfig (k + m) z.1)) = _
  rw [extendTriple_map_fst_thd _ _
    (fun x₁ x₂ y => rightWiredTripleStep_map_fst si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y)]
  exact upperHistoryPair_map_fst _ _ _ _ _

/-- The second FK marginal is exact. -/
theorem rightWiredTriple_map_snd
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) :
    (rightWiredTriple si ti so xo hq hp₀ hp₁ ζ₁ ζ₂).map (fun z => z.2.1) =
      rightWiredLaw si ti so xo hq hp₁ ζ₂ := by
  unfold rightWiredTriple
  rw [PMF.map_comp]
  rw [show (fun z : (Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool) => z.2.1) ∘
      decodeTriple = (fun z : List Bool × List Bool => toConfig (k + m) z.1) ∘
        (fun z : List Bool × List Bool × List Bool => (z.2.1, z.2.2)) from rfl]
  rw [← PMF.map_comp]
  change (((extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
    [] [] [] (k + m)).map (fun z => (z.2.1, z.2.2))).map
      (fun z : List Bool × List Bool => toConfig (k + m) z.1)) = _
  rw [extendTriple_map_snd_thd _ _
    (fun x₁ x₂ y => rightWiredTripleStep_map_snd si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y)]
  exact upperHistoryPair_map_fst _ _ _ _ _

/-- The upper marginal is the actual independent Bernoulli product on the
transported graph's finite edge labels. -/
theorem rightWiredTriple_map_thd
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) :
    (rightWiredTriple si ti so xo hq hp₀ hp₁ ζ₁ ζ₂).map (fun z => z.2.2) =
      (finIndexedGraph (U ⊕ K) (k + m)
        (transportedAmbient si ti so xo).source (transportedAmbient si ti so xo).target).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le) := by
  unfold rightWiredTriple
  rw [PMF.map_comp]
  rw [show (fun z : (Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool) => z.2.2) ∘
      decodeTriple = (fun z : List Bool × List Bool => toConfig (k + m) z.2) ∘
        (fun z : List Bool × List Bool × List Bool => (z.1, z.2.2)) from rfl]
  rw [← PMF.map_comp]
  change (((extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
    [] [] [] (k + m)).map (fun z => (z.1, z.2.2))).map
      (fun z : List Bool × List Bool => toConfig (k + m) z.2)) = _
  rw [extendTriple_map_fst_thd _ _
    (fun x₁ x₂ y => rightWiredTripleStep_map_fst si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y)]
  apply upperHistoryPair_map_snd_of_nextBit
  intro x hx
  exact nextBit_bernoulliProduct _ _
    (finIndexedGraph (U ⊕ K) (k + m)
      (transportedAmbient si ti so xo).source (transportedAmbient si ti so xo).target).freeBoundary
    (upperRateNN_pos hp₀) (upperRateNN_lt_one hq hp₀ hp₁) x hx

/-- Both lower configurations are below the common upper configuration on
support. -/
theorem rightWiredTriple_ordered
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K)
    {z : (Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool)}
    (hz : z ∈ (rightWiredTriple si ti so xo hq hp₀ hp₁ ζ₁ ζ₂).support) :
    z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
  unfold rightWiredTriple at hz
  rw [PMF.mem_support_map_iff] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hstep : ∀ x₁ x₂ y w, w ∈
      (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y).support →
      w.1 ≤ w.2.2 ∧ w.2.1 ≤ w.2.2 := by
    intro x₁ x₂ y w hw
    exact gluedUpperStep_ordered _ _ _ _ _ _ _ _ _ _ _ hw
  obtain ⟨h₁, h₂⟩ := extendTriple_ordered _ hstep List.Forall₂.nil List.Forall₂.nil (k + m) hw
  exact ⟨toConfig_le_of_forall₂ h₁, toConfig_le_of_forall₂ h₂⟩

end FK.Exploration.RightWiredSequential
