import FK.Glauber
import FK.FKGlauber

/-!
# The one-point part determines a finite random-cluster law

The paper (arXiv:2512.16486v1, Section 1.3) records that a positive
specification is characterised by its singleton part, and uses that to reduce
the `Phi`-Gibbs property to the one-edge conditional probabilities (see the
discussion after equation (5), and the role of item (2) of Proposition 1.8 in
the proof of Theorem 5.1).  This file proves that reduction at the level of
finite laws.

Main statements:

* `Glauber.FinProb.eq_of_shared_edgeConditionals`: two finite laws on a
  Boolean product with the same off-edge conditional families and full support
  coincide.
* `Glauber.FinProb.eq_fkPMF_of_shared_conditionals`: a full-support law whose
  singleton conditionals are those of the finite random-cluster law
  `G.fkPMF` *is* that random-cluster law.
* `Glauber.FinProb.ratio_eq`: the mass ratio of two full-support laws sharing
  a singleton conditional family is globally constant.

The proof is elementary: inside one off-edge fibre both laws factor through
the same conditional law, so the ratio of their masses is constant along the
fibre; a single-coordinate change moves inside one fibre, and any two
configurations are joined by finitely many single-coordinate changes.  Hence
the ratio of the two laws is a globally constant `c`, and summing gives
`c = 1`.

Nothing here asserts the infinite-volume DLR equations: passing the singleton
formula to an infinite-volume weak limit is a separate analytic step, recorded
as a residual in `ONE-POINT-DETERMINATION.md`.
-/

noncomputable section

open scoped BigOperators

namespace Glauber

namespace FinProb

open OpenPath

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

/-! ### Overwriting a list of coordinates -/

/-- Overwrite the coordinates listed in `L` by the corresponding values of
`target`, in list order.  This realises an arbitrary change of configuration as
a chain of single-coordinate changes. -/
def overwrite (source target : E → B) (L : List E) : E → B :=
  L.foldl (fun cfg e => Function.update cfg e (target e)) source

omit [Fintype E] [Fintype B] in
lemma overwrite_cons (source target : E → B) (a : E) (l : List E) :
    overwrite source target (a :: l) =
      overwrite (Function.update source a (target a)) target l := rfl

omit [Fintype E] [Fintype B] in
/-- After processing a list, a coordinate takes its target value exactly when
it occurred in the list. -/
lemma overwrite_apply (source target : E → B) (L : List E) (e : E) :
    overwrite source target L e = if e ∈ L then target e else source e := by
  induction L generalizing source with
  | nil => simp [overwrite]
  | cons a l ih =>
      rw [overwrite_cons, ih]
      by_cases hl : e ∈ l
      · simp [hl]
      · by_cases hea : e = a
        · subst hea
          simp [hl]
        · rw [Function.update_of_ne hea]
          simp [hl, hea]

/-- Overwriting all coordinates of `E` yields the target configuration. -/
lemma overwrite_univ_eq (source target : E → B) :
    overwrite source target (Finset.univ : Finset E).val.toList = target := by
  funext e
  rw [overwrite_apply]
  simp

/-! ### The cross-multiplied fibre identity -/

/-- The mass ratio of two laws with the same singleton conditional family is
unchanged by a single-coordinate change. -/
theorem ratio_update_eq {μ ν : OpenPath.FinProb (E → B)} {c : EdgeConditionals B E}
    (hμ : ∀ e, HasEdgeConditional μ c e) (hν : ∀ e, HasEdgeConditional ν c e)
    (hνpos : ∀ ω, 0 < ν.mass ω) (e : E) (ω : E → B) (b : B) :
    μ.mass ω / ν.mass ω = μ.mass (Function.update ω e b) / ν.mass (Function.update ω e b) := by
  classical
  set off : OffConfig B E e := (configSplit B e ω).1 with hoff
  have hupd : ∀ y : B, Function.update ω e y = (configSplit B e).symm (off, y) := by
    intro y
    rw [hoff]
    exact (configSplit_symm_update e ω y).symm
  have hμy : ∀ y : B, μ.mass (Function.update ω e y) =
      outsideMassConj (configSplit B e) μ off * (c e off).mass y := by
    intro y
    rw [hupd y]
    exact hμ e off y
  have hνy : ∀ y : B, ν.mass (Function.update ω e y) =
      outsideMassConj (configSplit B e) ν off * (c e off).mass y := by
    intro y
    rw [hupd y]
    exact hν e off y
  have hself : Function.update ω e (ω e) = ω := by
    funext x
    by_cases hx : x = e
    · subst hx; simp
    · rw [Function.update_of_ne hx]
  have hμω : μ.mass ω =
      outsideMassConj (configSplit B e) μ off * (c e off).mass (ω e) := by
    have h := hμy (ω e)
    rwa [hself] at h
  have hνω : ν.mass ω =
      outsideMassConj (configSplit B e) ν off * (c e off).mass (ω e) := by
    have h := hνy (ω e)
    rwa [hself] at h
  have hcross : μ.mass ω * ν.mass (Function.update ω e b) =
      ν.mass ω * μ.mass (Function.update ω e b) := by
    rw [hμω, hνω, hμy b, hνy b]
    ring
  rw [div_eq_div_iff (ne_of_gt (hνpos ω)) (ne_of_gt (hνpos (Function.update ω e b)))]
  simpa only [mul_comm] using hcross

/-- The mass ratio of two full-support laws with the same singleton
conditional family is globally constant. -/
theorem ratio_eq {μ ν : OpenPath.FinProb (E → B)} {c : EdgeConditionals B E}
    (hμ : ∀ e, HasEdgeConditional μ c e) (hν : ∀ e, HasEdgeConditional ν c e)
    (hνpos : ∀ ω, 0 < ν.mass ω) (ω ω' : E → B) :
    μ.mass ω / ν.mass ω = μ.mass ω' / ν.mass ω' := by
  have hchain : ∀ (L : List E) (σ : E → B),
      μ.mass σ / ν.mass σ = μ.mass (overwrite σ ω' L) / ν.mass (overwrite σ ω' L) := by
    intro L
    induction L with
    | nil => intro σ; simp [overwrite]
    | cons a l ih =>
        intro σ
        rw [overwrite_cons]
        exact (ratio_update_eq hμ hν hνpos a σ (ω' a)).trans (ih _)
  have h := hchain (Finset.univ : Finset E).val.toList ω
  rwa [overwrite_univ_eq] at h

/-! ### The one-point determination theorem -/

set_option linter.unusedVariables false in
/-- **The one-point part determines the law.**  Two full-support laws on a
finite Boolean product which share every off-edge conditional family coincide. -/
theorem eq_of_shared_edgeConditionals {μ ν : OpenPath.FinProb (E → B)}
    {c : EdgeConditionals B E}
    (hμ : ∀ e, HasEdgeConditional μ c e) (hν : ∀ e, HasEdgeConditional ν c e)
    (hμpos : ∀ ω, 0 < μ.mass ω) (hνpos : ∀ ω, 0 < ν.mass ω) :
    μ = ν := by
  classical
  have hne : (Finset.univ : Finset (E → B)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have h1 := μ.sum_mass
    rw [hempty] at h1
    simp at h1
  obtain ⟨ω₀, -⟩ := hne
  set r₀ : ℝ := μ.mass ω₀ / ν.mass ω₀ with hr₀
  have hconst : ∀ ω, μ.mass ω / ν.mass ω = r₀ := fun ω =>
    ratio_eq hμ hν hνpos ω ω₀
  have hmass : ∀ ω, μ.mass ω = r₀ * ν.mass ω := by
    intro ω
    have hω := hconst ω
    rw [div_eq_iff (ne_of_gt (hνpos ω))] at hω
    exact hω
  have hsum : (1 : ℝ) = r₀ := by
    have htot : ∑ ω, μ.mass ω = ∑ ω, r₀ * ν.mass ω :=
      Finset.sum_congr rfl fun ω _ => hmass ω
    rw [μ.sum_mass, ← Finset.mul_sum, ν.sum_mass, mul_one] at htot
    exact htot
  have hrone : r₀ = 1 := hsum.symm
  ext ω
  rw [hmass ω, hrone, one_mul]


/-! ### Invariance determines the conditional family -/

section Invariance

attribute [local instance] Classical.decEq

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The mass of one conjugated refresh step at an arbitrary configuration. -/
lemma refreshConj_mass {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (ρ : α ≃ β × γ) (c : β → OpenPath.FinProb γ) (a z : α) :
    (refreshConj ρ c a).mass z =
      if (ρ a).1 = (ρ z).1 then (c (ρ a).1).mass (ρ z).2 else 0 := by
  classical
  rw [refreshConj, OpenPath.FinProb.mass_map]
  have hcond : ∀ y' : γ,
      (ρ.symm ((ρ a).1, y') = z) ↔ ((ρ a).1 = (ρ z).1 ∧ y' = (ρ z).2) := by
    intro y'
    rw [show (ρ.symm ((ρ a).1, y') = z) ↔ (((ρ a).1, y') = ρ z) from
      ⟨fun h => by simpa using congrArg ρ h, fun h => by rw [h]; simp⟩]
    exact Prod.ext_iff
  simp only [hcond]
  by_cases ha : (ρ a).1 = (ρ z).1
  · have hiff : ∀ y' : γ, ((ρ a).1 = (ρ z).1 ∧ y' = (ρ z).2) ↔ y' = (ρ z).2 := by
      intro y'; rw [ha]; simp
    simp only [hiff]
    rw [Finset.sum_ite_eq']
    simp [ha]
  · have hiff : ∀ y' : γ, ¬((ρ a).1 = (ρ z).1 ∧ y' = (ρ z).2) := by
      intro y' h; exact ha h.1
    simp only [hiff, if_false, Finset.sum_const_zero]
    simp [ha]

/-- The one-step mass of a conjugated refresh at one point of a fibre.  This is
the computation used by `refreshConj_invariant`, isolated for reuse. -/
lemma bind_refreshConj_mass (ρ : α ≃ β × γ) (μ : OpenPath.FinProb α)
    (c : β → OpenPath.FinProb γ) (b : β) (y : γ) :
    (μ.bind (refreshConj ρ c)).mass (ρ.symm (b, y)) =
      outsideMassConj ρ μ b * (c b).mass y := by
  classical
  rw [OpenPath.FinProb.mass_bind]
  have hterm : ∀ a : α, μ.mass a * (refreshConj ρ c a).mass (ρ.symm (b, y)) =
      (if (ρ a).1 = b then μ.mass a else 0) * (c b).mass y := by
    intro a
    rw [refreshConj_mass]
    have h1 : (ρ (ρ.symm (b, y))).1 = b := by simp
    have h2 : (ρ (ρ.symm (b, y))).2 = y := by simp
    rw [h1, h2]
    by_cases hb : (ρ a).1 = b
    · simp [hb]
    · simp [hb]
  have hout : (∑ a, if (ρ a).1 = b then μ.mass a else 0) = outsideMassConj ρ μ b := by
    have h := Equiv.sum_comp ρ (fun x : β × γ => if x.1 = b then μ.mass (ρ.symm x) else 0)
    rw [outsideMassConj, ← sum_prod_ite_fst b (fun x : β × γ => μ.mass (ρ.symm x)), ← h]
    exact Finset.sum_congr rfl fun a _ => by simp
  calc ∑ a, μ.mass a * (refreshConj ρ c a).mass (ρ.symm (b, y))
      = ∑ a, (if (ρ a).1 = b then μ.mass a else 0) * (c b).mass y :=
        Finset.sum_congr rfl fun a _ => hterm a
    _ = (∑ a, if (ρ a).1 = b then μ.mass a else 0) * (c b).mass y := by
        rw [Finset.sum_mul]
    _ = outsideMassConj ρ μ b * (c b).mass y := by rw [hout]

/-- A law invariant under a conjugated coordinate refresh satisfies the
corresponding product conditional factorization. -/
theorem hasConjConditional_of_invariant {μ : OpenPath.FinProb α} {ρ : α ≃ β × γ}
    {c : β → OpenPath.FinProb γ} (h : Invariant μ (refreshConj ρ c)) :
    HasConjConditional ρ μ c := by
  intro b y
  have hb := congrArg (fun ν : OpenPath.FinProb α => ν.mass (ρ.symm (b, y))) h
  rw [bind_refreshConj_mass] at hb
  exact hb.symm

end Invariance

/-- Invariance under every singleton heat-bath update of a family determines
that family's conditionals. -/
theorem hasEdgeConditional_of_invariant {μ : OpenPath.FinProb (E → B)}
    {c : EdgeConditionals B E} (h : ∀ e, Invariant μ (edgeUpdate c e)) :
    ∀ e, HasEdgeConditional μ c e := by
  intro e
  exact hasConjConditional_of_invariant (h e)

/-- Invariance under a singleton heat-bath update is equivalent to satisfying
that update's conditional factorization, provided the law has full support on
the updated coordinate's fibres (which holds automatically for the FK law at
interior parameters). -/
theorem invariant_iff_hasEdgeConditional {μ : OpenPath.FinProb (E → B)}
    {c : EdgeConditionals B E} (e : E) :
    Invariant μ (edgeUpdate c e) ↔ HasEdgeConditional μ c e := by
  constructor
  · intro h
    exact hasConjConditional_of_invariant h
  · intro h
    exact edgeUpdate_invariant μ c h

set_option linter.unusedVariables false in
/-- **Uniqueness of the invariant law.**  Two full-support laws invariant under
the same singleton heat-bath family coincide.  Together with
`Glauber.edgeUpdate_invariant` this identifies the random-cluster law as the
unique full-support invariant law of its own one-edge conditional dynamics. -/
theorem eq_of_forall_invariant {μ ν : OpenPath.FinProb (E → B)}
    {c : EdgeConditionals B E} (hμ : ∀ e, Invariant μ (edgeUpdate c e))
    (hν : ∀ e, Invariant ν (edgeUpdate c e))
    (hμpos : ∀ ω, 0 < μ.mass ω) (hνpos : ∀ ω, 0 < ν.mass ω) :
    μ = ν :=
  eq_of_shared_edgeConditionals (hasEdgeConditional_of_invariant hμ)
    (hasEdgeConditional_of_invariant hν) hμpos hνpos

/-! ### Strictly positive conditional families force full support

The paper's *positive specification* hypothesis says that every conditional
probability lies strictly between `0` and `1`.  Under that hypothesis the
full-support assumption on the two laws of
`eq_of_shared_edgeConditionals` is automatic, so the one-point part determines
the law with no extra assumption on the laws themselves. -/

section StrictPositivity

variable {c : EdgeConditionals B E}

/-- Updating a coordinate with its own value changes nothing. -/
lemma hself_lemma {E B : Type*} [DecidableEq E] (e : E) (ω : E → B) :
    Function.update ω e (ω e) = ω := by
  funext x
  by_cases hx : x = e
  · subst hx; simp
  · rw [Function.update_of_ne hx]

/-- With a strictly positive conditional family, changing one coordinate
preserves the vanishing of the mass. -/
theorem mass_eq_zero_iff_update (hc : ∀ e off b, 0 < (c e off).mass b)
    {μ : OpenPath.FinProb (E → B)} (hμ : ∀ e, HasEdgeConditional μ c e)
    (e : E) (ω : E → B) (b : B) :
    μ.mass ω = 0 ↔ μ.mass (Function.update ω e b) = 0 := by
  classical
  set off : OffConfig B E e := (configSplit B e ω).1 with hoff
  have hupd : ∀ y : B, Function.update ω e y = (configSplit B e).symm (off, y) := by
    intro y
    rw [hoff]
    exact (configSplit_symm_update e ω y).symm
  have hμy : ∀ y : B, μ.mass (Function.update ω e y) =
      outsideMassConj (configSplit B e) μ off * (c e off).mass y := by
    intro y
    rw [hupd y]
    exact hμ e off y
  have hω : μ.mass ω =
      outsideMassConj (configSplit B e) μ off * (c e off).mass (ω e) := by
    have h := hμy (ω e)
    rwa [hself_lemma (ω := ω) (e := e)] at h
  rw [hω, hμy b]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rw [h']; ring
    · exact absurd h' (ne_of_gt (hc e off (ω e)))
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · rw [h']; ring
    · exact absurd h' (ne_of_gt (hc e off b))

/-- With a strictly positive conditional family, two configurations either both
have zero mass or both have positive mass. -/
theorem mass_eq_zero_iff (hc : ∀ e off b, 0 < (c e off).mass b)
    {μ : OpenPath.FinProb (E → B)} (hμ : ∀ e, HasEdgeConditional μ c e)
    (ω ω' : E → B) :
    μ.mass ω = 0 ↔ μ.mass ω' = 0 := by
  have hchain : ∀ (L : List E) (σ : E → B),
      (μ.mass σ = 0 ↔ μ.mass (overwrite σ ω' L) = 0) := by
    intro L
    induction L with
    | nil => intro σ; simp [overwrite]
    | cons a l ih =>
        intro σ
        rw [overwrite_cons]
        exact (mass_eq_zero_iff_update hc hμ a σ (ω' a)).trans (ih _)
  have h := hchain (Finset.univ : Finset E).val.toList ω
  rwa [overwrite_univ_eq] at h

/-- A law satisfying a strictly positive conditional family has full support. -/
theorem fullSupport_of_hasEdgeConditional (hc : ∀ e off b, 0 < (c e off).mass b)
    {μ : OpenPath.FinProb (E → B)} (hμ : ∀ e, HasEdgeConditional μ c e) :
    ∀ ω, 0 < μ.mass ω := by
  have hex : ∃ ω : E → B, μ.mass ω ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : ∑ ω, μ.mass ω = 0 := Finset.sum_eq_zero fun ω _ => h ω
    rw [μ.sum_mass] at hzero
    norm_num at hzero
  obtain ⟨ω₀, hω₀⟩ := hex
  have hω₀pos : 0 < μ.mass ω₀ := lt_of_le_of_ne (μ.mass_nonneg ω₀) (Ne.symm hω₀)
  intro ω
  have hiff := mass_eq_zero_iff hc hμ ω ω₀
  exact lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm fun h => hω₀ (hiff.mp h))

set_option linter.unusedVariables false in
/-- **The one-point part determines the law for a positive specification.**  Two
laws sharing a strictly positive off-edge conditional family coincide; no full
support hypothesis on either law is needed, because strict positivity forces it. -/
theorem eq_of_shared_edgeConditionals_of_strictlyPositive {μ ν : OpenPath.FinProb (E → B)}
    (hc : ∀ e off b, 0 < (c e off).mass b)
    (hμ : ∀ e, HasEdgeConditional μ c e) (hν : ∀ e, HasEdgeConditional ν c e) :
    μ = ν :=
  eq_of_shared_edgeConditionals hμ hν (fullSupport_of_hasEdgeConditional hc hμ)
    (fullSupport_of_hasEdgeConditional hc hν)

end StrictPositivity

end FinProb

end Glauber

/-! ### The random-cluster law as its own one-point part -/

namespace Glauber.FinProb

open FK.Finite

attribute [local instance] Classical.decEq

/-- At interior parameters every finite random-cluster configuration has
strictly positive mass. -/
lemma ofPMF_fkPMF_mass_pos {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : G.BoundaryPartition)
    (ω : G.Edge → Bool) :
    0 < (ofPMF (G.fkPMF hq hp₁.le ξ)).mass ω := by
  rw [ofPMF_mass]
  have hpos : 0 < G.fkPMF hq hp₁.le ξ ω := by
    rw [LabelledMultigraph.fkPMF_apply]
    exact ENNReal.coe_pos.mpr (div_pos
      (G.fkWeight_pos hq hp₀ hp₁ ξ ω)
      (G.partitionFunction_pos hq hp₁.le ξ))
  exact ENNReal.toReal_pos hpos.ne' (PMF.apply_ne_top _ _)

set_option linter.unusedVariables false in
/-- **A full-support law with the random-cluster singleton conditionals is the
random-cluster law.**  This is the finite form of the passage from the one-edge
conditional probabilities after equation (5) of the source to the `Phi`-Gibbs
property. -/
theorem eq_fkPMF_of_shared_conditionals {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : G.BoundaryPartition)
    {μ : OpenPath.FinProb (G.Edge → Bool)}
    (hμ : ∀ e, HasEdgeConditional μ (FKBridge.edgeConditionals G hq hp₁.le ξ) e)
    (hμpos : ∀ ω, 0 < μ.mass ω) :
    μ = ofPMF (G.fkPMF hq hp₁.le ξ) :=
  eq_of_shared_edgeConditionals hμ
    (fun e => FKBridge.fk_hasEdgeConditional G hq hp₁.le ξ e)
    hμpos (ofPMF_fkPMF_mass_pos hq hp₀ hp₁ ξ)


/-- At interior parameters the equation-(2) open rate is strictly between `0`
and `1`, so the random-cluster conditional family is a positive specification. -/
lemma openRate_mem_Ioo {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : OffConfig Bool G.Edge e) :
    FKBridge.openRate G (q := q) (p := p) ξ e off ∈ Set.Ioo (0 : ℝ) 1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp₀
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp₁
  have hden : (0 : ℝ) < (p : ℝ) + (q : ℝ) * (1 - (p : ℝ)) := by nlinarith
  have hprime0 : (0 : ℝ) < FK.prime (q : ℝ) (p : ℝ) := by
    rw [FK.prime]; exact div_pos hp0R hden
  have hprime1 : FK.prime (q : ℝ) (p : ℝ) < 1 := by
    rw [FK.prime, div_lt_one hden]; nlinarith
  constructor
  · unfold FKBridge.openRate
    split_ifs
    · exact hp0R
    · exact hprime0
  · unfold FKBridge.openRate
    split_ifs
    · exact hp1R
    · exact hprime1

/-- The random-cluster conditional family is strictly positive at interior
parameters, i.e. it is a positive specification in the sense of the source. -/
lemma edgeConditionals_strictlyPositive {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : G.BoundaryPartition) :
    ∀ (e : G.Edge) (off : OffConfig Bool G.Edge e) (b : Bool),
      0 < (FKBridge.edgeConditionals G hq hp₁.le ξ e off).mass b := by
  intro e off b
  have hI := openRate_mem_Ioo hq hp₀ hp₁ ξ e off
  cases b
  · rw [show (FKBridge.edgeConditionals G hq hp₁.le ξ e off).mass false =
        1 - FKBridge.openRate G (q := q) (p := p) ξ e off from by
      simp only [FKBridge.edgeConditionals, FKBridge.boolLaw_false]]
    linarith [hI.2]
  · rw [show (FKBridge.edgeConditionals G hq hp₁.le ξ e off).mass true =
        FKBridge.openRate G (q := q) (p := p) ξ e off from by
      simp only [FKBridge.edgeConditionals, FKBridge.boolLaw_true]]
    exact hI.1

/-- The one-point part of equation (2), in odds form, forces the conditional
family of the finite random-cluster law. -/
theorem hasEdgeConditional_of_openRate_odds {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp₁ : p < 1) (ξ : G.BoundaryPartition)
    {μ : OpenPath.FinProb (G.Edge → Bool)}
    (h : ∀ (e : G.Edge) (off : OffConfig Bool G.Edge e),
      μ.mass ((configSplit Bool e).symm (off, true)) *
          (1 - FKBridge.openRate G (q := q) (p := p) ξ e off) =
        μ.mass ((configSplit Bool e).symm (off, false)) *
          FKBridge.openRate G (q := q) (p := p) ξ e off) :
    ∀ e, HasEdgeConditional μ (FKBridge.edgeConditionals G hq hp₁.le ξ) e := by
  classical
  intro e
  unfold HasEdgeConditional HasConjConditional
  intro off b
  set r : ℝ := FKBridge.openRate G (q := q) (p := p) ξ e off with hr
  have hout : outsideMassConj (configSplit Bool e) μ off =
      μ.mass ((configSplit Bool e).symm (off, true)) +
        μ.mass ((configSplit Bool e).symm (off, false)) := by
    rw [outsideMassConj, Fintype.sum_bool]
  have htrue : (FKBridge.edgeConditionals G hq hp₁.le ξ e off).mass true = r := by
    simp only [FKBridge.edgeConditionals, FKBridge.boolLaw_true, hr]
  have hfalse : (FKBridge.edgeConditionals G hq hp₁.le ξ e off).mass false = 1 - r := by
    simp only [FKBridge.edgeConditionals, FKBridge.boolLaw_false, hr]
  have hkey := h e off
  rw [← hr] at hkey
  cases b
  · rw [hout, hfalse]
    linear_combination (-1 : ℝ) * hkey
  · rw [hout, htrue]
    linear_combination hkey

set_option linter.unusedVariables false in
/-- **The paper's one-point part identifies the random-cluster law.**  If a law
on the configurations of a finite labelled multigraph has the one-edge
conditional probabilities of equation (2) of the source — namely `p` when the
two endpoints of `e` are connected in the off-edge configuration and
`p' = p / (p + q(1-p))` otherwise, expressed in odds form so that no division
by a possibly vanishing conditional mass is needed — then the law *is* the
finite random-cluster law.  No full-support hypothesis on the law is required:
at interior parameters the conditional family is strictly positive, which
forces full support. -/
theorem eq_fkPMF_of_openRate_odds {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : G.BoundaryPartition)
    {μ : OpenPath.FinProb (G.Edge → Bool)}
    (h : ∀ (e : G.Edge) (off : OffConfig Bool G.Edge e),
      μ.mass ((configSplit Bool e).symm (off, true)) *
          (1 - FKBridge.openRate G (q := q) (p := p) ξ e off) =
        μ.mass ((configSplit Bool e).symm (off, false)) *
          FKBridge.openRate G (q := q) (p := p) ξ e off) :
    μ = ofPMF (G.fkPMF hq hp₁.le ξ) :=
  eq_of_shared_edgeConditionals_of_strictlyPositive
    (edgeConditionals_strictlyPositive hq hp₀ hp₁ ξ)
    (hasEdgeConditional_of_openRate_odds hq hp₁ ξ h)
    (fun e => FKBridge.fk_hasEdgeConditional G hq hp₁.le ξ e)

end Glauber.FinProb

#print axioms Glauber.FinProb.ratio_update_eq
#print axioms Glauber.FinProb.ratio_eq
#print axioms Glauber.FinProb.bind_refreshConj_mass
#print axioms Glauber.FinProb.hasConjConditional_of_invariant
#print axioms Glauber.FinProb.hasEdgeConditional_of_invariant
#print axioms Glauber.FinProb.eq_of_forall_invariant
#print axioms Glauber.FinProb.eq_of_shared_edgeConditionals
#print axioms Glauber.FinProb.ofPMF_fkPMF_mass_pos
#print axioms Glauber.FinProb.eq_fkPMF_of_shared_conditionals
#print axioms Glauber.FinProb.invariant_iff_hasEdgeConditional
#print axioms Glauber.FinProb.mass_eq_zero_iff_update
#print axioms Glauber.FinProb.mass_eq_zero_iff
#print axioms Glauber.FinProb.fullSupport_of_hasEdgeConditional
#print axioms Glauber.FinProb.eq_of_shared_edgeConditionals_of_strictlyPositive
#print axioms Glauber.FinProb.openRate_mem_Ioo
#print axioms Glauber.FinProb.edgeConditionals_strictlyPositive
#print axioms Glauber.FinProb.hasEdgeConditional_of_openRate_odds
#print axioms Glauber.FinProb.eq_fkPMF_of_openRate_odds
