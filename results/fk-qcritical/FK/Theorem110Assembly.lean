import FK.ReverseMartingale
import FK.TailConditionalTriviality
import FK.StrongUniqueness
import FK.ConventionEndpoints

/-!
# Theorem 1.9/1.10: the two remaining logical steps, assembled

Stage 18, direction 8.  This file proves, with no `sorry`/`axiom`/`unsafe`, the
two logical steps that the paper (arXiv:2512.16486v1, §5.1) uses to pass from a
percolation-type domination statement to *strong* uniqueness, and isolates
exactly what is left over.

* `FK.ae_nonPercolating_of_orderedCoupling`: a single monotone coupling to a
  non-percolating law forces the lower law to be non-percolating.  This is the
  step "This implies that `φ`-a.s. there is no infinite cluster" in the proof of
  Theorem 1.10.  The existing `ae_nonPercolating_of_orderedTripleCoupling`
  handles two lower laws sharing one upper marginal; the one-sided form used by
  the paper is derived here.
* `FK.InfiniteVolume.eq_of_unique_fkLimit`: Proposition 1.8(1) together with the
  tail Choquet decomposition shows that if the class of FK limit measures is the
  singleton `{μ₀}`, then *every* member of the total FK family
  `⋃_Φ 𝒢^Φ ∪ 𝒲` is `μ₀`.  This is the paper's sentence "According to item (1)
  of the above Proposition, strong uniqueness is equivalent to the uniqueness of
  the FK limit measure", in the direction that is used for Theorem 1.10.
* `FK.InfiniteVolume.existsUnique_fkLimit_iff_existsUnique_fkFamily`: the
  corresponding equivalence of `∃!` statements.

Nothing here assumes the conclusion: the only inputs are the repo's already
proved Proposition 1.8(1) weak-limit inclusion and the proved tail Choquet
decomposition of DLR classes.  What remains for Theorems 1.9/1.10 after this file
is Theorem 5.1 of the paper (uniqueness of one convention class under domination
by a non-percolating law); see the accompanying notes.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace FK

/-! ## Single-sided domination transfers non-percolation -/

variable {V : Type*}

/-- If `μ` is coupled to `ρ` so that the `μ`-coordinate is pointwise below the
`ρ`-coordinate, and `ρ` is almost surely non-percolating, then `μ` is almost
surely non-percolating.

This is the one-sided form of `ae_lower_of_orderedTripleCoupling` that the proof
of Theorem 1.10 uses: the event `NonPercolating G` is a lower set, so under the
coupling it pulls back from the upper marginal to the lower marginal. -/
theorem ae_nonPercolating_of_orderedCoupling (G : SimpleGraph V) [Countable V]
    [G.LocallyFinite] (hG : G.Connected)
    {μ ρ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ]
    {γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool))}
    (hγfst : γ.map Prod.fst = μ) (hγsnd : γ.map Prod.snd = ρ)
    (horder : ∀ᵐ z ∂γ, z.1 ≤ z.2)
    (hρ : ∀ᵐ ω ∂ρ, ω ∈ NonPercolating G) :
    ∀ᵐ ω ∂μ, ω ∈ NonPercolating G := by
  set B := NonPercolating G with hBdef
  have hB : MeasurableSet B := measurableSet_nonPercolating G hG
  have hρc : ρ Bᶜ = 0 := by
    have h := hρ
    rw [ae_iff] at h
    exact h
  have hup : γ {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | z.2 ∉ B} = 0 := by
    have h : (γ.map Prod.snd) Bᶜ = 0 := by
      rw [hγsnd]
      exact hρc
    rwa [Measure.map_apply measurable_snd hB.compl] at h
  have hordnull : γ {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | ¬ z.1 ≤ z.2} = 0 := by
    have h := horder
    rw [ae_iff] at h
    exact h
  have hlow : γ {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | z.1 ∉ B} = 0 := by
    have hsub : {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | z.1 ∉ B} ⊆
        {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | z.2 ∉ B} ∪
          {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | ¬ z.1 ≤ z.2} := by
      rintro ⟨x, y⟩ hx
      by_cases hxy : x ≤ y
      · exact Or.inl (fun hy => hx (isLowerSet_nonPercolating G hxy hy))
      · exact Or.inr hxy
    have hz : γ ({z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | z.2 ∉ B} ∪
          {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | ¬ z.1 ≤ z.2}) = 0 := by
      refine le_antisymm ?_ zero_le
      calc γ ({z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | z.2 ∉ B} ∪
            {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | ¬ z.1 ≤ z.2})
          ≤ γ {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | z.2 ∉ B} +
            γ {z : (G.edgeSet → Bool) × (G.edgeSet → Bool) | ¬ z.1 ≤ z.2} :=
            measure_union_le _ _
        _ = 0 := by rw [hup, hordnull, add_zero]
    exact measure_mono_null hsub hz
  have hμc : μ Bᶜ = 0 := by
    have h : (γ.map Prod.fst) Bᶜ = 0 := by
      rw [Measure.map_apply measurable_fst hB.compl]
      exact hlow
    rwa [hγfst] at h
  have h := hμc
  rw [ae_iff]
  exact h

end FK

namespace FK.InfiniteVolume

universe u v

variable {E : Type u} [Countable E]

/-- The paper's total FK family at `(p,q)`: the union of all boundary-convention
DLR classes together with the class of FK weak limits.

This is `FK(p,q) = ⋃_Φ 𝒢^Φ_{p,q} ∪ 𝒲_{p,q}` in the notation of the paper.  The
union here is over *all* measurable boundary assignments, coherent or not, which
only makes the family larger; the conclusion below is therefore the stronger
one. -/
def FKFamily (exh : BoxExhaustion.{u, v} E) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) : Set (ProbabilityMeasure (Configuration E)) :=
  (⋃ Φ : BoundaryAssignment exh.box, DLRMeasures exh Φ hq hp) ∪
    FKLimitMeasures exh hq hp

theorem mem_fkFamily_of_mem_dlr {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, v} E) {Φ : BoundaryAssignment exh.box}
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) : μ ∈ FKFamily exh hq hp :=
  Or.inl (Set.mem_iUnion.mpr ⟨Φ, hμ⟩)

theorem mem_fkFamily_of_mem_fkLimit {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, v} E) {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ FKLimitMeasures exh hq hp) : μ ∈ FKFamily exh hq hp :=
  Or.inr hμ

/-- **Proposition 1.8(1) + Choquet, in the direction used for Theorem 1.10.**

If every FK limit measure equals `μ₀`, then every member of the total FK family
equals `μ₀`.

Every extremal DLR law of a convention is an FK limit measure
(`mem_fkLimitMeasures_of_extremal_dlr`, Proposition 1.8(1)), so under the
hypothesis all extremal laws of every class coincide with `μ₀`; the proved tail
Choquet decomposition (`eq_dlr_of_extremal_unique`) then identifies the whole
class.  No class is assumed nonempty: an empty class contributes nothing. -/
theorem eq_of_unique_fkLimit {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, v} E) {μ₀ : ProbabilityMeasure (Configuration E)}
    (hW : ∀ μ : ProbabilityMeasure (Configuration E),
      μ ∈ FKLimitMeasures exh hq hp → μ = μ₀) :
    ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKFamily exh hq hp → ν = μ₀ := by
  intro ν hν
  rcases hν with hν | hν
  · obtain ⟨Φ, hν⟩ := Set.mem_iUnion.mp hν
    refine eq_dlr_of_extremal_unique exh Φ hq hp ν μ₀ hν ?_
    intro ξ hξ
    obtain ⟨η, hη, hcoe⟩ := hξ.1
    have hξ' : FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration E) ↦
          (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (η : Measure (Configuration E)) := by
      have hcast : (η : Measure (Configuration E)) = (ξ : Measure (Configuration E)) := hcoe
      rw [hcast]
      exact hξ
    have hlim : η ∈ FKLimitMeasures exh hq hp :=
      mem_fkLimitMeasures_of_extremal_dlr exh Φ hq hp η hη hξ'
    have hημ : η = μ₀ := hW η hlim
    have hval : (η : Measure (Configuration E)) = (μ₀ : Measure (Configuration E)) :=
      congrArg (fun x : ProbabilityMeasure (Configuration E) ↦
        (x : Measure (Configuration E))) hημ
    exact Subtype.ext (hcoe.symm.trans hval)
  · exact hW ν hν

/-- The converse direction: a singleton total FK family forces every FK limit
measure to equal that point. -/
theorem eq_of_unique_fkFamily {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, v} E) {μ₀ : ProbabilityMeasure (Configuration E)}
    (h : ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKFamily exh hq hp → ν = μ₀)
    {μ : ProbabilityMeasure (Configuration E)} (hμ : μ ∈ FKLimitMeasures exh hq hp) :
    μ = μ₀ :=
  h μ (mem_fkFamily_of_mem_fkLimit hq hp exh hμ)

/-- **Strong uniqueness is equivalent to uniqueness of the FK limit measure**
(Beffara–Faipeur–Oke, after Proposition 1.8(1)), in `∃!` form. -/
theorem existsUnique_fkFamily_iff_existsUnique_fkLimit {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (exh : BoxExhaustion.{u, v} E)
    (hne : (FKLimitMeasures exh hq hp).Nonempty) :
    (∃! μ : ProbabilityMeasure (Configuration E), μ ∈ FKLimitMeasures exh hq hp) ↔
      (∃! μ : ProbabilityMeasure (Configuration E), μ ∈ FKFamily exh hq hp) := by
  constructor
  · rintro ⟨μ₀, hμ₀, huniq⟩
    refine ⟨μ₀, mem_fkFamily_of_mem_fkLimit hq hp exh hμ₀, ?_⟩
    intro ν hν
    exact eq_of_unique_fkLimit hq hp exh (fun μ hμ => huniq μ hμ) ν hν
  · rintro ⟨μ₀, _hμ₀, huniq⟩
    obtain ⟨w, hw⟩ := hne
    have hw₀ : w = μ₀ := huniq w (mem_fkFamily_of_mem_fkLimit hq hp exh hw)
    refine ⟨w, hw, ?_⟩
    intro μ hμ
    have hμ₀ : μ = μ₀ := huniq μ (mem_fkFamily_of_mem_fkLimit hq hp exh hμ)
    exact hμ₀.trans hw₀.symm

/-- **Theorem 1.10 modulo Theorem 5.1 and Proposition 1.8(2).**

`h5_1` is exactly the conclusion of Theorem 5.1 of arXiv:2512.16486v1 for the
chosen boundary convention `Φ`: under domination by a non-percolating law, its
DLR class is a singleton.  `h518` is Proposition 1.8(2): every FK limit measure
with at most one infinite cluster is Gibbs for every convention.  Everything
else — that these two inputs give *strong* uniqueness of `FK (p,q)` — is proved
here, through Proposition 1.8(1) and the Choquet decomposition.

Neither input is a reformulation of the conclusion: `h5_1` is about one
convention class and `h518` is a Gibbs-property statement, while the conclusion
is about the union of *all* convention classes together with the weak-limit
class. -/
theorem theorem_1_10_modulo_theorem_5_1 {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {μ₀ : ProbabilityMeasure (Configuration E)}
    (h5_1 : DLRMeasures exh Φ hq hp = {μ₀})
    (h518 : ∀ μ : ProbabilityMeasure (Configuration E),
      μ ∈ FKLimitMeasures exh hq hp → μ ∈ DLRMeasures exh Φ hq hp) :
    (∀ μ : ProbabilityMeasure (Configuration E),
        μ ∈ FKLimitMeasures exh hq hp → μ = μ₀) ∧
      (∃! μ : ProbabilityMeasure (Configuration E), μ ∈ FKFamily exh hq hp) := by
  have hW : ∀ μ : ProbabilityMeasure (Configuration E),
      μ ∈ FKLimitMeasures exh hq hp → μ = μ₀ := by
    intro μ hμ
    have hmem : μ ∈ DLRMeasures exh Φ hq hp := h518 μ hμ
    rw [h5_1] at hmem
    exact Set.mem_singleton_iff.mp hmem
  refine ⟨hW, ⟨μ₀, ?_, ?_⟩⟩
  · exact mem_fkFamily_of_mem_dlr hq hp exh (by rw [h5_1]; exact Set.mem_singleton_iff.mpr rfl)
  · intro ν hν
    exact eq_of_unique_fkLimit hq hp exh hW ν hν

end FK.InfiniteVolume

namespace FK.InfiniteVolume

universe u v

variable {E : Type u} [Countable E]

local instance setoidMeasurableSpaceStage18 (V : Type*) : MeasurableSpace (Setoid V) := ⊤

/-- The constant free-boundary assignment: measurability is automatic because
boundary partitions carry the discrete measurable structure. -/
def freeAssignment (exh : BoxExhaustion.{u, v} E) : BoundaryAssignment exh.box where
  partition := fun n _ => FK.Finite.LabelledMultigraph.freeBoundary (G := (exh.box n).graph)
  measurable_partition := fun _ => measurable_const

/-- **Unconditional instance: strong uniqueness at zero rate.**

At `p = 0` the finite FK law is the all-closed point mass for *every* boundary
partition, so every convention class and every FK weak limit is the single law
`closedLaw E`.  Consequently the total FK family is a singleton, for every
`q > 0` and every exhaustion.

This is a `q`-unconditional instance of the paper's strong uniqueness, and it
shows that the assembly `eq_of_unique_fkLimit` is not vacuous. -/
theorem fkFamily_zero_eq_singleton (exh : BoxExhaustion.{u, v} E) {q : NNReal}
    (hq : 0 < q) :
    FKFamily exh hq (p := 0) bot_le = {FK.MainIntegration.Endpoint.closedLaw E} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · -- the point mass belongs to every convention class
    exact mem_fkFamily_of_mem_dlr (hq := hq) (hp := bot_le) exh (Φ := freeAssignment exh)
      (μ := FK.MainIntegration.Endpoint.closedLaw E)
      (by rw [ConventionTransport.dlrMeasures_zero_eq_singleton exh (freeAssignment exh) hq]
          exact Set.mem_singleton _)
  · intro ν hν
    rcases hν with hν | hν
    · obtain ⟨Φ, hν⟩ := Set.mem_iUnion.mp hν
      rw [ConventionTransport.dlrMeasures_zero_eq_singleton exh Φ hq] at hν
      exact Set.mem_singleton_iff.mp hν
    · exact FK.MainIntegration.Endpoint.limitOrGibbs_eq_closedLaw_zero exh hq
        (Or.inl hν)

/-- **Unconditional instance: strong uniqueness at unit rate.** -/
theorem fkFamily_one_eq_singleton (exh : BoxExhaustion.{u, v} E) {q : NNReal}
    (hq : 0 < q) :
    FKFamily exh hq (p := 1) le_rfl = {FK.MainIntegration.Endpoint.openLaw E} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · exact mem_fkFamily_of_mem_dlr (hq := hq) (hp := le_rfl) exh (Φ := freeAssignment exh)
      (μ := FK.MainIntegration.Endpoint.openLaw E)
      (by rw [ConventionTransport.dlrMeasures_one_eq_singleton exh (freeAssignment exh) hq]
          exact Set.mem_singleton _)
  · intro ν hν
    rcases hν with hν | hν
    · obtain ⟨Φ, hν⟩ := Set.mem_iUnion.mp hν
      rw [ConventionTransport.dlrMeasures_one_eq_singleton exh Φ hq] at hν
      exact Set.mem_singleton_iff.mp hν
    · exact FK.MainIntegration.Endpoint.limitOrGibbs_eq_openLaw_one exh hq
        (Or.inl hν)

end FK.InfiniteVolume

namespace FK.InfiniteVolume

universe u v

variable {E : Type u} [Countable E]

/-- **The FK weak-limit class is nonempty for a suitable exhaustion.**

Compactness of the space of probability measures on a countable Boolean product
supplies a convergent subsequence of any sequence of finite-volume laws.  The
subsequence is itself a genuine `BoxExhaustion`, so the limit is an `IsFKLimit`
for that exhaustion.  This is the form in which compactness gives existence in
the paper; note that it does *not* give nonemptiness of `FKLimitMeasures exh`
for an arbitrary fixed exhaustion, since `IsFKLimit` requires convergence along
the whole sequence and the boundary partitions may be chosen adversarially. -/
theorem exists_boxExhaustion_fkLimitMeasures_nonempty (exh : BoxExhaustion.{u, v} E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    ∃ exh' : BoxExhaustion.{u, v} E, (FKLimitMeasures exh' hq hp).Nonempty := by
  classical
  let α : ∀ n, (exh.box n).BoundaryPartition :=
    fun n => (freeAssignment exh).partition n (fun _ => false)
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq
    (fun n => (exh.box n).finiteVolumeLaw hq hp (α n))
  have hmono : Monotone (fun n => (exh.box (φ n)).edges) :=
    fun a b hab => exh.monotone (hφ.monotone hab)
  have hcov : ∀ e : E, ∃ n, e ∈ (exh.box (φ n)).edges := by
    intro e
    obtain ⟨N, hN⟩ := exh.covers e
    obtain ⟨n, hn⟩ := (hφ.tendsto_atTop.eventually (eventually_ge_atTop N)).exists
    exact ⟨n, exh.monotone hn hN⟩
  refine ⟨⟨fun n => exh.box (φ n), hmono, hcov⟩, ν, fun n => α (φ n), ?_⟩
  exact hν

end FK.InfiniteVolume
