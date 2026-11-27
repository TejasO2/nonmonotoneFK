import FK.SourceUniqueness
import FK.MainIntegration
import FK.AGShift
import FK.EndpointIntegration

/-!
# The AG upper window as the dominant in source strong uniqueness

This file joins Proposition 4.2 to `FK.SourceUniqueness`.  It does not prove
essential enhancement or the nested equation (9).  It proves that those are
the only two inputs left after choosing the star/cycle devices: the separate
nonpercolating-dominant hypothesis is produced by the AG deactivation shift
and Proposition 4.2.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Topology Classical

namespace FK.SourceWindow

open FK.InfiniteVolume
open FK.SourceUniqueness
open FK.EssentialWindow
open CurvatureVariance.Infra.Percolation

universe u

/-- The upper Bernoulli product associated with a pair of source devices. -/
noncomputable def upperLaw {V : Type u} [Countable V] {G : SimpleGraph V}
    [G.LocallyFinite] (Sstar Scycle : Set G.edgeSet) (Delta L : ℕ)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    ProbabilityMeasure (Configuration G.edgeSet) :=
  FKLimit.bernoulliProduct
    (FK.Phases.upperWeights Sstar Scycle (Delta - 1) (L - 1)
      (show 0 ≤ (p : ℝ) by positivity)
      (show (p : ℝ) ≤ 1 by exact_mod_cast hp)
      (show 0 < (q : ℝ) by exact_mod_cast hq))

/-- The uniform separated star/cycle devices used by Proposition 4.2.  The
bounded-distance and double-ray fields are retained for the AG input, although
the stochastic comparison itself needs only the separated-device fields. -/
structure SourceEnhancementDevices {V : Type u} (G : SimpleGraph V)
    [G.LocallyFinite] where
  Delta : ℕ
  L : ℕ
  Sstar : Set G.edgeSet
  Scycle : Set G.edgeSet
  Dstar : G.edgeSet → Finset G.edgeSet
  Dcycle : G.edgeSet → Finset G.edgeSet
  separatedStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar
  separatedCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle
  boundedStar : FK.Theorem14.BoundedDistance G.lineGraph.dist Sstar
  boundedCycle : FK.Theorem14.BoundedDistance G.lineGraph.dist Scycle
  rayStar : ∀ e ∈ Sstar, FK.EssentialEnhancement.OnDoubleRay e
  rayCycle : ∀ e ∈ Scycle, FK.EssentialEnhancement.OnDoubleRay e
  cardStar : ∀ e ∈ Sstar, (Dstar e).card ≤ Delta
  cardCycle : ∀ e ∈ Scycle, (Dcycle e).card ≤ L
  starDevice : ∀ e ∈ Sstar, ∃ v : V,
    Dstar e = FK.QuasiTransitive.starDevice G v ∧ v ∈ (e : Sym2 V)
  cycleDevice : ∀ e ∈ Scycle, ∃ (v : V) (c : G.Walk v v),
    c.IsCycle ∧ c.length = L ∧
      Dcycle e = FK.QuasiTransitive.walkDevice c ∧ (e : Sym2 V) ∈ c.edges

/-- Quasi-transitivity transports one pivotal cycle/double-ray edge to the two
uniform device families required throughout the source argument. -/
theorem nonempty_sourceEnhancementDevices {V : Type u} [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] (hconn : G.Connected)
    (hqt : FK.QuasiTransitive.IsQuasiTransitive G)
    {u₀ : V} {e₀ : G.edgeSet} (hu₀ : u₀ ∈ (e₀ : Sym2 V))
    (hr₀ : FK.EssentialEnhancement.OnDoubleRay e₀)
    {v₀ : V} (c₀ : G.Walk v₀ v₀) (hc₀ : c₀.IsCycle)
    (he₀ : (e₀ : Sym2 V) ∈ c₀.edges) :
    Nonempty (SourceEnhancementDevices G) := by
  obtain ⟨Delta, Sstar, Dstar, -, hStar, hboundedStar, hrayStar,
    hcardStar, hstar⟩ :=
    FK.QuasiTransitive.exists_separated_star_devices G hconn hqt u₀ hu₀ hr₀
  obtain ⟨L, Scycle, Dcycle, -, hCycle, hboundedCycle, hrayCycle,
    hcardCycle, hcycle⟩ :=
    FK.QuasiTransitive.exists_separated_cycle_devices G hconn hqt c₀ hc₀ he₀ hr₀
  exact ⟨{
    Delta := Delta
    L := L
    Sstar := Sstar
    Scycle := Scycle
    Dstar := Dstar
    Dcycle := Dcycle
    separatedStar := hStar
    separatedCycle := hCycle
    boundedStar := hboundedStar
    boundedCycle := hboundedCycle
    rayStar := hrayStar
    rayCycle := hrayCycle
    cardStar := hcardStar
    cardCycle := hcardCycle
    starDevice := hstar
    cycleDevice := hcycle }⟩

/-- The accepted paper graph package supplies both the pivotal edge used for
nonempty tails and the uniform device data used in the windowed theorem. -/
theorem exists_pivot_and_sourceEnhancementDevices {V : Type u} [Countable V]
    {G : SimpleGraph V} [G.LocallyFinite] (o : V)
    (H : FK.AGShift.PaperGraphHypotheses G o) :
    ∃ e₀ : G.edgeSet, Nonempty (SourceEnhancementDevices G) := by
  obtain ⟨e₀, hr₀, v, c, hc, he⟩ := H.pivotal
  exact ⟨e₀, nonempty_sourceEnhancementDevices G H.connected H.quasiTransitive
    (FK.RandomClosedBoundary.edgeFst_mem e₀) hr₀ c hc he⟩

section Tail

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- Truncating an arbitrary finite initial segment preserves a source FK weak
limit and its source outer-boundary classes. -/
theorem isSourceFKLimit_tail (E : VertexExhaustion V) (k : ℕ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsSourceFKLimit hq hp E μ) :
    IsSourceFKLimit hq hp (E.tail k) μ := by
  obtain ⟨α, hα, hlim⟩ := hμ
  refine ⟨fun n => α (n + k), ?_, ?_⟩
  · intro n
    exact hα (n + k)
  · change Tendsto
      (fun n => ((E.tail k).box n).finiteVolumeLaw hq hp (α (n + k)))
      atTop (𝓝 μ)
    change Tendsto
      (fun n => (E.box (n + k)).finiteVolumeLaw hq hp (α (n + k)))
      atTop (𝓝 μ)
    exact hlim.comp (tendsto_add_atTop_nat k)

/-- After one fixed edge has entered an induced vertex exhaustion, every box
in the tail has nonempty edge type.  This discharges the technical nonempty
hypothesis of Proposition 4.2 without restricting the original exhaustion. -/
theorem exists_tail_nonempty_edges (E : VertexExhaustion V) (e : G.edgeSet) :
    ∃ k : ℕ, ∀ n : ℕ, Nonempty (((E.tail k).box (G := G) n).edges) := by
  obtain ⟨k, hk⟩ := E.growingFamily (G := G) |>.covers e
  refine ⟨k, fun n => ⟨⟨e, ?_⟩⟩⟩
  change e ∈ (E.box (G := G) (n + k)).edges
  have hle : k ≤ n + k := Nat.le_add_left k n
  exact E.growingFamily (G := G) |>.edges_mono k (n + k) hle e hk

end Tail

section ParameterIdentification

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal}

/-- In the `q < 1` regime, `upperLaw` is literally Proposition 4.2's upper
cycle-decrement product. -/
theorem upperLaw_eq_ltUpperParameters (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : q < 1) (Sstar Scycle : Set G.edgeSet) (Delta L : ℕ) :
    upperLaw Sstar Scycle Delta L hq hp1.le =
      FKLimit.bernoulliProduct
        (FKLimit.ltUpperParameters (p : ℝ) (q : ℝ)
          (show (p : ℝ) ∈ Ioo 0 1 by
            exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
          (show 0 < (q : ℝ) by exact_mod_cast hq)
          ((FKLimit.self_lt_fkSingletonParameter_iff
              (show (p : ℝ) ∈ Ioo 0 1 by
                exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
              (show 0 < (q : ℝ) by exact_mod_cast hq)).2
            (by exact_mod_cast hq1))
          L Scycle) := by
  let hp : (p : ℝ) ∈ Ioo 0 1 :=
    ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
    (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
  change FKLimit.bernoulliProduct _ = FKLimit.bernoulliProduct _
  rw [FK.MainIntegration.ltUpperParameters_eq_upperWeights hp hqR hpp
    Sstar Scycle Delta L]

/-- In the `1 < q` regime, `upperLaw` is literally Proposition 4.2's upper
star-decrement product. -/
theorem upperLaw_eq_gtUpperParameters (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 < q) (Sstar Scycle : Set G.edgeSet) (Delta L : ℕ) :
    upperLaw Sstar Scycle Delta L (lt_trans zero_lt_one hq1) hp1.le =
      FKLimit.bernoulliProduct
        (FKLimit.gtUpperParameters (p : ℝ) (q : ℝ)
          (show (p : ℝ) ∈ Ioo 0 1 by
            exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
          (show 0 < (q : ℝ) by exact_mod_cast (lt_trans zero_lt_one hq1))
          ((FKLimit.fkSingletonParameter_lt_self_iff
              (show (p : ℝ) ∈ Ioo 0 1 by
                exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
              (show 0 < (q : ℝ) by exact_mod_cast (lt_trans zero_lt_one hq1))).2
            (by exact_mod_cast hq1))
          Delta Sstar) := by
  let hp : (p : ℝ) ∈ Ioo 0 1 :=
    ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hq1)
  let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
    (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
  change FKLimit.bernoulliProduct _ = FKLimit.bernoulliProduct _
  rw [FK.MainIntegration.gtUpperParameters_eq_upperWeights hp hqR hpp
    Sstar Scycle Delta L]

end ParameterIdentification

section Domination

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal}

/-- Proposition 4.2 dominates every source weak limit by the exact upper
product, for `q < 1`.  The original exhaustion is unrestricted: a tail is used
only internally to satisfy the finite-box nonempty-edge premise. -/
theorem upperLaw_dominates_q_lt_one (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : q < 1) (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceWeakLimits (G := G) hq hp1.le) :
    FKLimit.StochasticallyDominates
      (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le) μ := by
  obtain ⟨E, hE⟩ := hμ
  obtain ⟨k, hne⟩ := exists_tail_nonempty_edges E e₀
  obtain ⟨α, hα, hlim⟩ := isSourceFKLimit_tail hq hp1.le E k hE
  have hcomp := FK.Prop42Source.proposition_4_2_lt
    ((E.tail k).exhaustion (G := G)) ((E.tail k).data (G := G))
    ((E.tail k).data_vertex_injective (G := G)) hq hp0 hp1 hq1
    (Or.inl ⟨α, hα, hlim⟩)
    D.Sstar D.Dstar D.Delta D.separatedStar D.starDevice D.cardStar
    D.Scycle D.Dcycle D.L D.separatedCycle D.cycleDevice D.cardCycle hne
  rw [upperLaw_eq_ltUpperParameters hq hp0 hp1 hq1
    D.Sstar D.Scycle D.Delta D.L]
  exact hcomp.2

/-- The corresponding upper domination for `1 < q`, where the decrement is on
the star set rather than the cycle set. -/
theorem upperLaw_dominates_one_lt_q (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 < q) (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceWeakLimits (G := G) (lt_trans zero_lt_one hq1) hp1.le) :
    FKLimit.StochasticallyDominates
      (upperLaw D.Sstar D.Scycle D.Delta D.L (lt_trans zero_lt_one hq1) hp1.le) μ := by
  obtain ⟨E, hE⟩ := hμ
  obtain ⟨k, hne⟩ := exists_tail_nonempty_edges E e₀
  obtain ⟨α, hα, hlim⟩ := isSourceFKLimit_tail (lt_trans zero_lt_one hq1)
    hp1.le E k hE
  have hcomp := FK.Prop42Source.proposition_4_2_gt
    ((E.tail k).exhaustion (G := G)) ((E.tail k).data (G := G))
    ((E.tail k).data_vertex_injective (G := G)) hp0 hp1 hq1
    (Or.inl ⟨α, hα, hlim⟩)
    D.Sstar D.Dstar D.Delta D.separatedStar D.starDevice D.cardStar
    D.Scycle D.Dcycle D.L D.separatedCycle D.cycleDevice D.cardCycle hne
  rw [upperLaw_eq_gtUpperParameters hp0 hp1 hq1
    D.Sstar D.Scycle D.Delta D.L]
  exact hcomp.2

end Domination

section ZeroEndpoint

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

lemma eq_of_openConnected_allClosed {x y : V}
    (h : OpenConnected G (fun _ => false) Set.univ x y) : x = y := by
  obtain ⟨p, hp⟩ := h
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      rw [isOpenIn_cons] at hp
      have hopen := hp.1.2
      simp at hopen

lemma nonPercolating_allClosed :
    (fun _ : G.edgeSet => false) ∈ FK.NonPercolating G := by
  intro o
  apply (Set.finite_singleton o).subset
  intro x hx
  exact Set.mem_singleton_iff.mpr (eq_of_openConnected_allClosed hx).symm

lemma ae_nonPercolating_closedLaw (hG : G.Connected) :
    ∀ᵐ ω ∂(FK.MainIntegration.Endpoint.closedLaw G.edgeSet :
      Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  change ∀ᵐ ω ∂(Measure.dirac (fun _ : G.edgeSet => false)),
    ω ∈ FK.NonPercolating G
  exact (mem_ae_dirac_iff (measurableSet_nonPercolating G hG)).2
    nonPercolating_allClosed

/-- Every member of the whole source family at zero rate is the all-closed
point mass.  For the DLR branch a single arbitrary vertex exhaustion suffices;
coherence or geometric compatibility is not used in the coordinate argument. -/
theorem eq_closedLaw_of_mem_sourceFKMeasures_zero [Nonempty V]
    {q : NNReal} (hq : 0 < q)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) hq (p := 0) bot_le) :
    μ = FK.MainIntegration.Endpoint.closedLaw G.edgeSet := by
  apply FK.MainIntegration.Endpoint.eq_closedLaw_of_ae_closed
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  rcases hμ with hμ | ⟨E, α, hα, hlim⟩
  · obtain ⟨Φ, hΦ, hμ⟩ := Set.mem_iUnion.mp hμ
    let E : VertexExhaustion V :=
      Classical.choice (VertexExhaustion.exists_vertexExhaustion (V := V))
    have hrestr : μ ∈ DLRMeasures (E.exhaustion (G := G)) (assignment E Φ)
        hq (p := 0) bot_le := mem_dlr_restrict hμ
    simpa using FK.MainIntegration.Endpoint.dlr_apply_open_zero
      (E.exhaustion (G := G)) (assignment E Φ) hq hrestr e
  · simpa using FK.MainIntegration.Endpoint.fkLimit_apply_open_zero
      (E.exhaustion (G := G)) hq α hlim e

/-- The complete source-family Theorem 1.10 conclusion at `p = 0`. -/
theorem sourceFKMeasures_zero [Nonempty V] (hG : G.Connected)
    {q : NNReal} (hq : 0 < q) :
    ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq (p := 0) bot_le = {μ₀} ∧
        ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)),
          ω ∈ FK.NonPercolating G := by
  obtain ⟨μ, hμ⟩ := sourceWeakLimits_nonempty (G := G) hq (p := 0) bot_le
  have hμclosed : μ = FK.MainIntegration.Endpoint.closedLaw G.edgeSet :=
    eq_closedLaw_of_mem_sourceFKMeasures_zero hq
      (mem_sourceFKMeasures_of_weak hq (p := 0) bot_le hμ)
  refine ⟨FK.MainIntegration.Endpoint.closedLaw G.edgeSet, ?_,
    ae_nonPercolating_closedLaw hG⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · rw [← hμclosed]
    exact mem_sourceFKMeasures_of_weak hq (p := 0) bot_le hμ
  · intro ν hν
    exact eq_closedLaw_of_mem_sourceFKMeasures_zero hq hν

end ZeroEndpoint

section MainWindow

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- **Theorem 1.10, antiferromagnetic upper window, modulo exactly Lemma
2.1 and the AG deactivation shift.**  Proposition 4.2 supplies the dominant;
the AG window supplies its nonpercolation.  No separate domination,
nonpercolation, weak-limit-existence, fixed-exhaustion, Theorem 5.1, or
Proposition 1.8(2) hypothesis remains. -/
theorem theorem_1_10_window_q_lt_one_of_nestedEquationNine
    (hG : G.Connected) (o : V)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (hdeact : FK.AGShift.DeactivationShift (Percolating G) (criticalProb G o)
      D.Scycle)
    (roots : Finset G.edgeSet → Finset V)
    (hEq9 : NestedEquationNine (G := G) hq hp1.le
      (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le) roots) :
    ∃ δ' : ℝ, 0 < δ' ∧
      (max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) <
          criticalProb G o + δ' →
        ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
          SourceFKMeasures (G := G) hq hp1.le = {μ₀} ∧
            ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)),
              ω ∈ FK.NonPercolating G) := by
  letI : Nonempty V := ⟨o⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
  obtain ⟨δ', hδ', hwin⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_q_lt_one
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) (q : ℝ) hqR hq1R
      (isUpperSet_percolating G) (measurableSet_percolating G hG)
      hdeact hpc0 hpc1
  refine ⟨δ', hδ', ?_⟩
  intro hpwindow
  let ρ := upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le
  have hpIcc : (p : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hp1.le⟩
  have hzero : (ρ : Measure (Configuration G.edgeSet)) (Percolating G) = 0 :=
    hwin (p : ℝ) hpIcc hpwindow
  have hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    (ae_nonPercolating_iff_measure_percolating_eq_zero G
      (ρ : Measure (Configuration G.edgeSet))).2 hzero
  have hdom : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceWeakLimits (G := G) hq hp1.le →
        FKLimit.StochasticallyDominates ρ μ := by
    intro μ hμ
    exact upperLaw_dominates_q_lt_one hq hp0 hp1 hq1 D e₀ hμ
  exact FK.SourceUniqueness.theorem_1_10_modulo_AG_window_and_lemma_2_1
    hq hp1.le ρ hρ roots hEq9 hdom

/-- **Theorem 1.10, `1 < q` upper window, modulo exactly Lemma 2.1 and the
AG deactivation shift.**  In this regime Proposition 4.2 decrements the star
set, so that is the set occurring in `hdeact`. -/
theorem theorem_1_10_window_one_lt_q_of_nestedEquationNine
    (hG : G.Connected) (o : V)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (hdeact : FK.AGShift.DeactivationShift (Percolating G) (criticalProb G o)
      D.Sstar)
    (roots : Finset G.edgeSet → Finset V)
    (hEq9 : NestedEquationNine (G := G) (lt_trans zero_lt_one hq1) hp1.le
      (upperLaw D.Sstar D.Scycle D.Delta D.L (lt_trans zero_lt_one hq1) hp1.le)
      roots) :
    ∃ δ' : ℝ, 0 < δ' ∧
      (max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) <
          criticalProb G o + δ' →
        ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
          SourceFKMeasures (G := G) (lt_trans zero_lt_one hq1) hp1.le = {μ₀} ∧
            ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)),
              ω ∈ FK.NonPercolating G) := by
  letI : Nonempty V := ⟨o⟩
  let hq : 0 < q := lt_trans zero_lt_one hq1
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : 1 < (q : ℝ) := by exact_mod_cast hq1
  obtain ⟨δ', hδ', hwin⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_one_lt_q
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) (q : ℝ) hqR hq1R
      (isUpperSet_percolating G) (measurableSet_percolating G hG)
      hdeact hpc0 hpc1
  refine ⟨δ', hδ', ?_⟩
  intro hpwindow
  let ρ := upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le
  have hpIcc : (p : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hp1.le⟩
  have hzero : (ρ : Measure (Configuration G.edgeSet)) (Percolating G) = 0 :=
    hwin (p : ℝ) hpIcc hpwindow
  have hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    (ae_nonPercolating_iff_measure_percolating_eq_zero G
      (ρ : Measure (Configuration G.edgeSet))).2 hzero
  have hdom : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceWeakLimits (G := G) hq hp1.le →
        FKLimit.StochasticallyDominates ρ μ := by
    intro μ hμ
    exact upperLaw_dominates_one_lt_q hp0 hp1 hq1 D e₀ hμ
  exact FK.SourceUniqueness.theorem_1_10_modulo_AG_window_and_lemma_2_1
    hq hp1.le ρ hρ roots hEq9 hdom

end MainWindow

section FullParameterWindow

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- Zero percolation of the selected upper law plus Lemma 2.1 gives the exact
source conclusion in the `q < 1` case. -/
theorem unique_of_upperLaw_zero_q_lt_one [Nonempty V]
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (roots : Finset G.edgeSet → Finset V)
    (hEq9 : NestedEquationNine (G := G) hq hp1.le
      (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le) roots)
    (hzero : (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le :
      Measure (Configuration G.edgeSet)) (Percolating G) = 0) :
    ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp1.le = {μ₀} ∧
        ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)),
          ω ∈ FK.NonPercolating G := by
  let ρ := upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le
  have hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    (ae_nonPercolating_iff_measure_percolating_eq_zero G
      (ρ : Measure (Configuration G.edgeSet))).2 hzero
  have hdom : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceWeakLimits (G := G) hq hp1.le →
        FKLimit.StochasticallyDominates ρ μ := by
    intro μ hμ
    exact upperLaw_dominates_q_lt_one hq hp0 hp1 hq1 D e₀ hμ
  exact FK.SourceUniqueness.theorem_1_10_modulo_AG_window_and_lemma_2_1
    hq hp1.le ρ hρ roots hEq9 hdom

/-- The `1 < q` companion of `unique_of_upperLaw_zero_q_lt_one`. -/
theorem unique_of_upperLaw_zero_one_lt_q [Nonempty V]
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (roots : Finset G.edgeSet → Finset V)
    (hEq9 : NestedEquationNine (G := G) (lt_trans zero_lt_one hq1) hp1.le
      (upperLaw D.Sstar D.Scycle D.Delta D.L (lt_trans zero_lt_one hq1) hp1.le)
      roots)
    (hzero : (upperLaw D.Sstar D.Scycle D.Delta D.L (lt_trans zero_lt_one hq1)
      hp1.le : Measure (Configuration G.edgeSet)) (Percolating G) = 0) :
    ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) (lt_trans zero_lt_one hq1) hp1.le = {μ₀} ∧
        ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)),
          ω ∈ FK.NonPercolating G := by
  let hq : 0 < q := lt_trans zero_lt_one hq1
  let ρ := upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le
  have hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    (ae_nonPercolating_iff_measure_percolating_eq_zero G
      (ρ : Measure (Configuration G.edgeSet))).2 hzero
  have hdom : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceWeakLimits (G := G) hq hp1.le →
        FKLimit.StochasticallyDominates ρ μ := by
    intro μ hμ
    exact upperLaw_dominates_one_lt_q hp0 hp1 hq1 D e₀ hμ
  exact FK.SourceUniqueness.theorem_1_10_modulo_AG_window_and_lemma_2_1
    hq hp1.le ρ hρ roots hEq9 hdom

/-- **Full upper-window Theorem 1.10 for `q < 1`, modulo only the ordinary
nested equation and AG deactivation shift.**  The radius is uniform over all
`p ≤ 1`; `p = 0` is proved directly and the window excludes `p = 1`. -/
theorem theorem_1_10_full_window_q_lt_one
    (hG : G.Connected) (o : V)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    {q : NNReal} (hq : 0 < q) (hq1 : q < 1)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (hdeact : FK.AGShift.DeactivationShift (Percolating G) (criticalProb G o)
      D.Scycle)
    (roots : Finset G.edgeSet → Finset V)
    (hEq9 : ∀ {p : NNReal} (hp0 : 0 < p) (hp1 : p < 1),
      NestedEquationNine (G := G) hq hp1.le
        (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le) roots) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ (p : NNReal) (hp : p ≤ 1),
      max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) <
          criticalProb G o + δ' →
        ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
          SourceFKMeasures (G := G) hq hp = {μ₀} ∧
            ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)),
              ω ∈ FK.NonPercolating G := by
  letI : Nonempty V := ⟨o⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
  obtain ⟨δ', hδ', hwin⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_q_lt_one
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) (q : ℝ) hqR hq1R
      (isUpperSet_percolating G) (measurableSet_percolating G hG)
      hdeact hpc0 hpc1
  let δ := min δ' ((1 - criticalProb G o) / 2)
  have hδ : 0 < δ := lt_min hδ' (by linarith)
  have hδleft : δ ≤ δ' := min_le_left _ _
  have hδright : δ ≤ (1 - criticalProb G o) / 2 := min_le_right _ _
  have hpcδ : criticalProb G o + δ < 1 := by linarith
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpwindow
  have hpwindow' : max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) <
      criticalProb G o + δ' :=
    hpwindow.trans_le (by linarith [hδleft])
  by_cases hpzero : p = 0
  · subst p
    exact sourceFKMeasures_zero hG hq
  · have hp0 : 0 < p := pos_iff_ne_zero.mpr hpzero
    have hp1ne : p ≠ 1 := by
      intro hpone
      have hponeR : (p : ℝ) = 1 := by exact_mod_cast hpone
      have hge : (1 : ℝ) ≤ max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) := by
        rw [hponeR]
        exact le_max_left _ _
      linarith [hge.trans_lt hpwindow]
    have hp1 : p < 1 := lt_of_le_of_ne hp hp1ne
    have hpIcc : (p : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by exact_mod_cast hp⟩
    have hzero : (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le :
        Measure (Configuration G.edgeSet)) (Percolating G) = 0 :=
      hwin (p : ℝ) hpIcc hpwindow'
    exact unique_of_upperLaw_zero_q_lt_one hq hp0 hp1 hq1 D e₀ roots
      (hEq9 hp0 hp1) hzero

/-- **Full upper-window Theorem 1.10 for `1 < q`, modulo only the ordinary
nested equation and AG deactivation shift on the star set.** -/
theorem theorem_1_10_full_window_one_lt_q
    (hG : G.Connected) (o : V)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    {q : NNReal} (hq1 : 1 < q)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (hdeact : FK.AGShift.DeactivationShift (Percolating G) (criticalProb G o)
      D.Sstar)
    (roots : Finset G.edgeSet → Finset V)
    (hEq9 : ∀ {p : NNReal} (hp0 : 0 < p) (hp1 : p < 1),
      NestedEquationNine (G := G) (lt_trans zero_lt_one hq1) hp1.le
        (upperLaw D.Sstar D.Scycle D.Delta D.L (lt_trans zero_lt_one hq1) hp1.le)
        roots) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ (p : NNReal) (hp : p ≤ 1),
      max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) <
          criticalProb G o + δ' →
        ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
          SourceFKMeasures (G := G) (lt_trans zero_lt_one hq1) hp = {μ₀} ∧
            ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)),
              ω ∈ FK.NonPercolating G := by
  letI : Nonempty V := ⟨o⟩
  let hq : 0 < q := lt_trans zero_lt_one hq1
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : 1 < (q : ℝ) := by exact_mod_cast hq1
  obtain ⟨δ', hδ', hwin⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_one_lt_q
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) (q : ℝ) hqR hq1R
      (isUpperSet_percolating G) (measurableSet_percolating G hG)
      hdeact hpc0 hpc1
  let δ := min δ' ((1 - criticalProb G o) / 2)
  have hδ : 0 < δ := lt_min hδ' (by linarith)
  have hδleft : δ ≤ δ' := min_le_left _ _
  have hδright : δ ≤ (1 - criticalProb G o) / 2 := min_le_right _ _
  have hpcδ : criticalProb G o + δ < 1 := by linarith
  refine ⟨δ, hδ, ?_⟩
  intro p hp hpwindow
  have hpwindow' : max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) <
      criticalProb G o + δ' :=
    hpwindow.trans_le (by linarith [hδleft])
  by_cases hpzero : p = 0
  · subst p
    exact sourceFKMeasures_zero hG hq
  · have hp0 : 0 < p := pos_iff_ne_zero.mpr hpzero
    have hp1ne : p ≠ 1 := by
      intro hpone
      have hponeR : (p : ℝ) = 1 := by exact_mod_cast hpone
      have hge : (1 : ℝ) ≤ max (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) := by
        rw [hponeR]
        exact le_max_left _ _
      linarith [hge.trans_lt hpwindow]
    have hp1 : p < 1 := lt_of_le_of_ne hp hp1ne
    have hpIcc : (p : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by exact_mod_cast hp⟩
    have hzero : (upperLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le :
        Measure (Configuration G.edgeSet)) (Percolating G) = 0 :=
      hwin (p : ℝ) hpIcc hpwindow'
    exact unique_of_upperLaw_zero_one_lt_q hp0 hp1 hq1 D e₀ roots
      (hEq9 hp0 hp1) hzero

end FullParameterWindow

end FK.SourceWindow
