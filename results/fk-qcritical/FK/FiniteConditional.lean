import FK.FiniteComponentCounts

/-!
# Conditional edge laws for normalized finite weights

The main result in this file is stated directly for the normalized finite PMF
implemented in `FiniteModel`.  The finite FK-specific weight ratios are added
below once the one-edge component identities are available.
-/

namespace FK.Finite.Conditional

noncomputable section
open scoped Classical ENNReal BigOperators
open FK.FiniteFiber
open FK.Finite.LabelledMultigraph

variable {E : Type*} [Fintype E]

/-- A positive-mass off-edge fibre for normalized finite weights has nonzero
sum of its open and closed unnormalised weights. -/
lemma weight_pair_ne_zero_of_support [DecidableEq E] (w : Config E → NNReal)
    (hw : 0 < ∑ a, w a) (e : E) (ω : Config E)
    (h : ∃ ξ ∈ offFiber e ω, ξ ∈ (normalizedPMFOfSumPos w hw).support) :
    w (withEdge e true ω) + w (withEdge e false ω) ≠ 0 := by
  classical
  rcases h with ⟨ξ, hξ, hμξ⟩
  rcases mem_offFiber_iff_eq.mp hξ with rfl | rfl
  · have hne : w (withEdge e true ω) ≠ 0 := by
      have hm := hμξ
      rw [normalizedPMFOfSumPos, PMF.mem_support_normalize_iff] at hm
      exact_mod_cast hm
    intro hs
    exact hne (add_eq_zero.mp hs).1
  · have hne : w (withEdge e false ω) ≠ 0 := by
      have hm := hμξ
      rw [normalizedPMFOfSumPos, PMF.mem_support_normalize_iff] at hm
      exact_mod_cast hm
    intro hs
    exact hne (add_eq_zero.mp hs).2

/-- Exact open-coordinate law after conditioning normalized finite weights on
all the other coordinates.  No strict inequality on either individual weight
is assumed. -/
theorem normalized_conditional_open_toReal [DecidableEq E] (w : Config E → NNReal)
    (hw : 0 < ∑ a, w a) (e : E) (ω : Config E)
    (h : ∃ ξ ∈ offFiber e ω, ξ ∈ (normalizedPMFOfSumPos w hw).support) :
    (((normalizedPMFOfSumPos w hw).filter (offFiber e ω) h).map
      (fun ξ => ξ e) true).toReal =
      (w (withEdge e true ω) : ℝ) /
        ((w (withEdge e true ω) : ℝ) + (w (withEdge e false ω) : ℝ)) := by
  classical
  have hw0 : (∑' a, (w a : ℝ≥0∞)) ≠ 0 := by
    rw [tsum_fintype]
    exact_mod_cast hw.ne'
  have hwtop : (∑' a, (w a : ℝ≥0∞)) ≠ ∞ := by
    simp [tsum_fintype]
  have hsum := weight_pair_ne_zero_of_support w hw e ω h
  have hsum' : (w (withEdge e true ω) : ℝ≥0∞) +
      (w (withEdge e false ω) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hsum
  have hratio := filter_map_coordinate_true_toReal
    (normalizedPMFOfSumPos w hw) e ω h
    (w (withEdge e true ω) : ℝ≥0∞) (w (withEdge e false ω) : ℝ≥0∞)
    (∑' a, (w a : ℝ≥0∞))⁻¹
    (by rw [normalizedPMFOfSumPos_apply])
    (by rw [normalizedPMFOfSumPos_apply])
    (ENNReal.inv_ne_zero.mpr hwtop) (ENNReal.inv_ne_top.mpr hw0)
    (by simp) (by simp) hsum'
  simpa using hratio

/-- The Bernoulli product with one labelled edge erased. -/
def offEdgeWeight (G : LabelledMultigraph) (p : NNReal) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge) : NNReal :=
  ∏ a ∈ Finset.univ.erase e, if ω a then p else 1 - p

lemma edgeWeight_open_factor (G : LabelledMultigraph) (p : NNReal) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge) :
    G.edgeWeight p (withEdge e true ω) = p * offEdgeWeight G p e ω := by
  unfold LabelledMultigraph.edgeWeight offEdgeWeight
  rw [← Finset.mul_prod_erase Finset.univ
    (fun a => if withEdge e true ω a then p else 1 - p) (Finset.mem_univ e)]
  simp only [withEdge_edge, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [withEdge_off (Finset.ne_of_mem_erase ha)]

lemma edgeWeight_closed_factor (G : LabelledMultigraph) (p : NNReal) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge) :
    G.edgeWeight p (withEdge e false ω) = (1 - p) * offEdgeWeight G p e ω := by
  unfold LabelledMultigraph.edgeWeight offEdgeWeight
  rw [← Finset.mul_prod_erase Finset.univ
    (fun a => if withEdge e false ω a then p else 1 - p) (Finset.mem_univ e)]
  simp only [withEdge_edge]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [withEdge_off (Finset.ne_of_mem_erase ha)]

lemma fkWeight_open_eq_of_connected (G : LabelledMultigraph) (q p : NNReal)
    (ξ : G.BoundaryPartition) (e : G.Edge) (ω : FiniteFiber.Config G.Edge)
    (hconn : endpointsConnectedWithout G ξ e ω) :
    G.fkWeight q p ξ (withEdge e true ω) =
      p * (offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e false ω)) := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_open_factor,
    componentCount_open_eq_of_connected G ξ e ω hconn]
  ring

lemma fkWeight_closed_eq_of_connected (G : LabelledMultigraph) (q p : NNReal)
    (ξ : G.BoundaryPartition) (e : G.Edge) (ω : FiniteFiber.Config G.Edge) :
    G.fkWeight q p ξ (withEdge e false ω) =
      (1 - p) * (offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e false ω)) := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_closed_factor]
  ring

lemma fkWeight_open_eq_of_not_connected (G : LabelledMultigraph) (q p : NNReal)
    (ξ : G.BoundaryPartition) (e : G.Edge) (ω : FiniteFiber.Config G.Edge) :
    G.fkWeight q p ξ (withEdge e true ω) =
      p * (offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e true ω)) := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_open_factor]
  ring

lemma fkWeight_closed_eq_of_not_connected (G : LabelledMultigraph) (q p : NNReal)
    (ξ : G.BoundaryPartition) (e : G.Edge) (ω : FiniteFiber.Config G.Edge)
    (hconn : ¬ endpointsConnectedWithout G ξ e ω) :
    G.fkWeight q p ξ (withEdge e false ω) =
      q * (1 - p) * (offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e true ω)) := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_closed_factor,
    ← componentCount_open_add_one_of_not_connected G ξ e ω hconn]
  simp only [pow_succ]
  ring

lemma fkWeight_pair_ne_zero_of_support (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (ω : FiniteFiber.Config G.Edge)
    (h : ∃ ξ' ∈ offFiber e ω, ξ' ∈ (G.fkPMF hq hp ξ).support) :
    G.fkWeight q p ξ (withEdge e true ω) + G.fkWeight q p ξ (withEdge e false ω) ≠ 0 := by
  have hw : 0 < ∑ a, G.fkWeight q p ξ a := by
    simpa only [LabelledMultigraph.partitionFunction] using G.partitionFunction_pos hq hp ξ
  unfold LabelledMultigraph.fkPMF at h
  exact weight_pair_ne_zero_of_support (G.fkWeight q p ξ) hw e ω h

lemma fk_conditional_weight_ratio (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (ω : FiniteFiber.Config G.Edge)
    (h : ∃ ξ' ∈ offFiber e ω, ξ' ∈ (G.fkPMF hq hp ξ).support) :
    (((G.fkPMF hq hp ξ).filter (offFiber e ω) h).map (fun ξ' => ξ' e) true).toReal =
      (G.fkWeight q p ξ (withEdge e true ω) : ℝ) /
        ((G.fkWeight q p ξ (withEdge e true ω) : ℝ) +
          (G.fkWeight q p ξ (withEdge e false ω) : ℝ)) := by
  have hw : 0 < ∑ a, G.fkWeight q p ξ a := by
    simpa only [LabelledMultigraph.partitionFunction] using G.partitionFunction_pos hq hp ξ
  unfold LabelledMultigraph.fkPMF at h ⊢
  exact normalized_conditional_open_toReal (G.fkWeight q p ξ) hw e ω h

/-- Equation (2) on the endpoint-connection event: the open conditional
probability is `p`, including `p = 0` and `p = 1`. -/
theorem fk_conditional_open_of_connected (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (ω : FiniteFiber.Config G.Edge)
    (hconn : endpointsConnectedWithout G ξ e ω)
    (h : ∃ ξ' ∈ offFiber e ω, ξ' ∈ (G.fkPMF hq hp ξ).support) :
    (((G.fkPMF hq hp ξ).filter (offFiber e ω) h).map (fun ξ' => ξ' e) true).toReal =
      (p : ℝ) := by
  let c : NNReal := offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e false ω)
  have hopen : G.fkWeight q p ξ (withEdge e true ω) = p * c := by
    dsimp [c]
    exact fkWeight_open_eq_of_connected G q p ξ e ω hconn
  have hclosed : G.fkWeight q p ξ (withEdge e false ω) = (1 - p) * c := by
    dsimp [c]
    exact fkWeight_closed_eq_of_connected G q p ξ e ω
  have hsum := fkWeight_pair_ne_zero_of_support G hq hp ξ e ω h
  have hc : c ≠ 0 := by
    intro hc
    apply hsum
    rw [hopen, hclosed, hc]
    simp
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  rw [fk_conditional_weight_ratio G hq hp ξ e ω h, hopen, hclosed]
  simp only [NNReal.coe_mul, NNReal.coe_sub hp, NNReal.coe_one]
  field_simp [hc']
  ring

/-- Equation (2) off the endpoint-connection event: the threshold is
`p / (p + q * (1-p))`, with the same endpoint coverage. -/
theorem fk_conditional_open_of_not_connected (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (ω : FiniteFiber.Config G.Edge)
    (hconn : ¬ endpointsConnectedWithout G ξ e ω)
    (h : ∃ ξ' ∈ offFiber e ω, ξ' ∈ (G.fkPMF hq hp ξ).support) :
    (((G.fkPMF hq hp ξ).filter (offFiber e ω) h).map (fun ξ' => ξ' e) true).toReal =
      FK.prime (q : ℝ) (p : ℝ) := by
  let c : NNReal := offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e true ω)
  have hopen : G.fkWeight q p ξ (withEdge e true ω) = p * c := by
    dsimp [c]
    exact fkWeight_open_eq_of_not_connected G q p ξ e ω
  have hclosed : G.fkWeight q p ξ (withEdge e false ω) = q * (1 - p) * c := by
    dsimp [c]
    exact fkWeight_closed_eq_of_not_connected G q p ξ e ω hconn
  have hsum := fkWeight_pair_ne_zero_of_support G hq hp ξ e ω h
  have hc : c ≠ 0 := by
    intro hc
    apply hsum
    rw [hopen, hclosed, hc]
    simp
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hd : (p : ℝ) + (q : ℝ) * (1 - (p : ℝ)) ≠ 0 :=
    (FK.denominator_pos (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)).ne'
  rw [fk_conditional_weight_ratio G hq hp ξ e ω h, hopen, hclosed]
  simp only [NNReal.coe_mul, NNReal.coe_sub hp, NNReal.coe_one]
  unfold FK.prime
  field_simp [hc', hd]

end
end FK.Finite.Conditional
