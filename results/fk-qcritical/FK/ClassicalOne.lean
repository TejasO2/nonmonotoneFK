import FK.FiniteComparison

/-!
# The classical `q = 1` finite FK law

At `q = 1` the wired component factor in the finite FK weight is identically
one.  We normalize the resulting Bernoulli edge product directly and identify
it with the actual finite FK PMF.  The statement permits loops, parallel
labelled edges, every boundary setoid, and both endpoints of `0 ≤ p ≤ 1`.
-/

namespace FK.Finite.LabelledMultigraph

open scoped BigOperators ENNReal Classical

open FK.Finite.Comparison

variable (G : LabelledMultigraph)

/-- The unnormalized Bernoulli edge masses sum to one over all Boolean
configurations. -/
lemma sum_edgeWeight {p : NNReal} (hp : p ≤ 1) :
    ∑ ω : G.Configuration, G.edgeWeight p ω = 1 := by
  classical
  let hr : ∀ _ : G.Edge, (p : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ => ⟨p.coe_nonneg, by exact_mod_cast hp⟩
  have hprod := (boolProduct (fun _ : G.Edge => (p : ℝ)) hr).sum_mass
  apply NNReal.eq
  rw [NNReal.coe_sum]
  simpa only [edgeWeight, NNReal.coe_prod, apply_ite, NNReal.coe_sub hp,
    NNReal.coe_one, boolProduct, OpenPath.FinProb.pi_mass, boolLaw] using hprod

/-- At `q = 1`, the FK partition function is independent of the arbitrary
boundary partition and equals one. -/
lemma partitionFunction_q_one {p : NNReal} (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) : G.partitionFunction 1 p ξ = 1 := by
  simpa only [partitionFunction, fkWeight, one_pow, mul_one] using G.sum_edgeWeight hp

/-- Independent Bernoulli labelled edges, normalized as a PMF on the actual
finite FK configuration space. -/
noncomputable def bernoulliProductPMF {p : NNReal} (hp : p ≤ 1) :
    PMF G.Configuration :=
  PMF.ofFintype (fun ω => (G.edgeWeight p ω : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, G.sum_edgeWeight hp, ENNReal.coe_one])

@[simp] lemma bernoulliProductPMF_apply {p : NNReal} (hp : p ≤ 1)
    (ω : G.Configuration) : G.bernoulliProductPMF hp ω = G.edgeWeight p ω := by
  simp [bernoulliProductPMF]

/-- **The finite FK law at `q = 1` is exactly Bernoulli percolation.**  No
interiority, graph simplicity, or boundary-partition hypothesis is needed. -/
theorem fkPMF_q_one {p : NNReal} (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    G.fkPMF (q := 1) zero_lt_one hp ξ = G.bernoulliProductPMF hp := by
  apply PMF.ext
  intro ω
  rw [LabelledMultigraph.fkPMF_apply, G.partitionFunction_q_one hp,
    G.bernoulliProductPMF_apply]
  simp [fkWeight]

/-- Measure-valued form of the classical FK/Bernoulli identity. -/
theorem fkMeasure_q_one {p : NNReal} (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    G.fkMeasure (q := 1) zero_lt_one hp ξ = (G.bernoulliProductPMF hp).toMeasure := by
  rw [fkMeasure, G.fkPMF_q_one hp]

/-- The explicit product PMF has the same real-mass presentation as the
independent `FinProb` product already used by the finite comparison machinery. -/
lemma ofPMF_bernoulliProductPMF {p : NNReal} (hp : p ≤ 1) :
    Glauber.ofPMF (G.bernoulliProductPMF hp) =
      boolProduct (fun _ : G.Edge => (p : ℝ))
        (fun _ => ⟨p.coe_nonneg, by exact_mod_cast hp⟩) := by
  apply OpenPath.FinProb.ext
  intro ω
  simp only [Glauber.ofPMF_mass, G.bernoulliProductPMF_apply, ENNReal.coe_toReal,
    edgeWeight, boolProduct, OpenPath.FinProb.pi_mass, NNReal.coe_prod, apply_ite,
    NNReal.coe_sub hp, NNReal.coe_one, boolLaw]

/-- Real-mass bridge from the actual FK PMF at `q = 1` to the established
independent finite product law. -/
theorem ofPMF_fkPMF_q_one {p : NNReal} (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    Glauber.ofPMF (G.fkPMF (q := 1) zero_lt_one hp ξ) =
      boolProduct (fun _ : G.Edge => (p : ℝ))
        (fun _ => ⟨p.coe_nonneg, by exact_mod_cast hp⟩) := by
  rw [G.fkPMF_q_one hp]
  exact G.ofPMF_bernoulliProductPMF hp

/-- Endpoint consistency with the previously verified all-closed FK law. -/
@[simp] lemma bernoulliProductPMF_zero :
    G.bernoulliProductPMF (p := 0) bot_le = PMF.pure G.allClosed := by
  rw [← G.fkPMF_q_one (p := 0) bot_le G.freeBoundary]
  exact G.fkPMF_zero (q := 1) zero_lt_one G.freeBoundary

/-- Endpoint consistency with the previously verified all-open FK law. -/
@[simp] lemma bernoulliProductPMF_one :
    G.bernoulliProductPMF (p := 1) le_rfl = PMF.pure G.allOpen := by
  rw [← G.fkPMF_q_one (p := 1) le_rfl G.freeBoundary]
  exact G.fkPMF_one (q := 1) zero_lt_one G.freeBoundary

end FK.Finite.LabelledMultigraph
