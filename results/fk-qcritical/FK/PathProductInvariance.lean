import FK.Proposition32
import FK.JointProductInvariance
import FK.OrderedFinite

noncomputable section

open scoped BigOperators Classical
open Set Filter

namespace PathProduct

open OpenPath Glauber

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

def AgreeOutside (s t : E → B) (l : List E) : Prop :=
  ∀ f, f ∉ l → s f = t f

lemma agreeOutside_update_cons {l : List E} {f : E} (hf : f ∉ l)
    (s t : E → B) (b : B) :
    AgreeOutside (Function.update s f b) t l ↔
      b = t f ∧ AgreeOutside s t (f :: l) := by
  constructor
  · intro h
    have hbf : b = t f := by
      have := h f hf
      simpa using this
    refine ⟨hbf, ?_⟩
    intro g hg
    have hgl : g ∉ l := by
      intro hgl
      exact hg (by simp [hgl])
    have hgf : g ≠ f := by
      intro hgf
      subst g
      exact hg (by simp)
    have := h g hgl
    simpa [Function.update_of_ne hgf] using this
  · rintro ⟨hbf, h⟩ g hg
    by_cases hgf : g = f
    · subst g
      simpa using hbf
    · have hg' : g ∉ f :: l := by simp [hgf, hg]
      have := h g hg'
      simpa [Function.update_of_ne hgf] using this

/-- Exact transition mass for a duplicate-free sweep of coordinate updates
whose laws are independent of the off-edge configuration. -/
theorem sweep_edgeUpdate_constant_mass (c : EdgeConditionals B E)
    (ν : E → OpenPath.FinProb B) :
    ∀ (l : List E), l.Nodup →
      (∀ f ∈ l, ∀ off, c f off = ν f) → ∀ s t : E → B,
      (sweep (l.map (edgeUpdate c)) s).mass t =
        (l.map fun f => (ν f).mass (t f)).prod *
          if AgreeOutside s t l then 1 else 0 := by
  intro l hl
  induction l with
  | nil =>
      intro _ s t
      simp [sweep, Glauber.FinProb.dirac, OpenPath.FinProb.mass_bind,
        AgreeOutside, funext_iff, eq_comm]
  | cons f l ih =>
      intro hc s t
      have hl' : l.Nodup := (List.nodup_cons.mp hl).2
      have hf : f ∉ l := (List.nodup_cons.mp hl).1
      have hcf : c f (fun g => s g.1) = ν f := hc f (by simp) _
      simp only [List.map_cons, sweep, Glauber.seq]
      rw [edgeUpdate_eq_map, hcf, GlauberCoupling.bind_map]
      simp only [OpenPath.FinProb.mass_bind]
      have hc' : ∀ g ∈ l, ∀ off, c g off = ν g := by
        intro g hg off
        exact hc g (by simp [hg]) off
      simp_rw [ih hl' hc']
      by_cases hst : AgreeOutside s t (f :: l)
      · have hagree (b : B) : AgreeOutside (Function.update s f b) t l ↔
            b = t f := by
          rw [agreeOutside_update_cons hf]
          exact and_iff_left hst
        simp [hagree, hst, mul_assoc, mul_comm, mul_left_comm]
      · have hagree (b : B) : ¬ AgreeOutside (Function.update s f b) t l := by
          intro h
          exact hst ((agreeOutside_update_cons hf s t b).mp h).2
        simp [hagree, hst]

end PathProduct

namespace PathProduct

open OpenPath Glauber

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

/-- Exact mass after an edge-dependent update followed by a duplicate-free
sweep of off-independent updates. -/
theorem edgeUpdate_then_sweep_constant_mass (c : EdgeConditionals B E)
    (ν : E → OpenPath.FinProb B) (e : E) (l : List E)
    (hl : l.Nodup) (he : e ∉ l)
    (hc : ∀ f ∈ l, ∀ off, c f off = ν f) (s t : E → B) :
    ((edgeUpdate c e s).bind (sweep (l.map (edgeUpdate c)))).mass t =
      (c e (fun f => s f.1)).mass (t e) *
        (l.map fun f => (ν f).mass (t f)).prod *
          if AgreeOutside s t (e :: l) then 1 else 0 := by
  rw [edgeUpdate_eq_map, GlauberCoupling.bind_map]
  simp only [OpenPath.FinProb.mass_bind]
  simp_rw [sweep_edgeUpdate_constant_mass c ν l hl hc]
  by_cases hst : AgreeOutside s t (e :: l)
  · have hagree (b : B) : AgreeOutside (Function.update s e b) t l ↔
        b = t e := by
      rw [agreeOutside_update_cons he]
      exact and_iff_left hst
    simp [hagree, hst, mul_assoc]
  · have hagree (b : B) : ¬ AgreeOutside (Function.update s e b) t l := by
      intro h
      exact hst ((agreeOutside_update_cons he s t b).mp h).2
    simp [hagree, hst]

end PathProduct

namespace PathProduct

open OpenPath Glauber
open JointInvariance

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

@[simp] lemma indexedBlockEquiv_apply_enhanced (e : E) (A : Finset E) (s : E → B) :
    (indexedBlockEquiv e A s).1.1 = s e := by
  simp [indexedBlockEquiv, Equiv.piSplitAt, Equiv.piEquivPiSubtypeProd]

@[simp] lemma indexedBlockEquiv_apply_aux (e : E) (A : Finset E) (s : E → B)
    (a : AuxiliaryIndex E e A) :
    (indexedBlockEquiv e A s).1.2 a = s a.1.1 := by
  have hne : (a.1.1 : E) ≠ e := a.1.2
  have hA : (a.1.1 : E) ∈ A := a.2
  simp [indexedBlockEquiv, Equiv.piSplitAt, Equiv.piEquivPiSubtypeProd, hne, hA]

@[simp] lemma indexedBlockEquiv_apply_rest (e : E) (A : Finset E) (s : E → B)
    (r : RemainingIndex E e A) :
    (indexedBlockEquiv e A s).2 r = s r.1.1 := by
  have hne : (r.1.1 : E) ≠ e := r.1.2
  have hA : (r.1.1 : E) ∉ A := r.2
  simp [indexedBlockEquiv, Equiv.piSplitAt, Equiv.piEquivPiSubtypeProd, hne, hA]

@[simp] lemma indexedBlockEquiv_symm_apply_enhanced (e : E) (A : Finset E)
    (b : B) (a : AuxiliaryIndex E e A → B) (r : RemainingIndex E e A → B) :
    (indexedBlockEquiv e A).symm ⟨⟨b, a⟩, r⟩ e = b := by
  simp [indexedBlockEquiv, Equiv.piSplitAt, Equiv.piEquivPiSubtypeProd]

@[simp] lemma indexedBlockEquiv_symm_apply_aux (e : E) (A : Finset E)
    (b : B) (a : AuxiliaryIndex E e A → B) (r : RemainingIndex E e A → B)
    (x : AuxiliaryIndex E e A) :
    (indexedBlockEquiv e A).symm ⟨⟨b, a⟩, r⟩ x.1.1 = a x := by
  have hne : (x.1.1 : E) ≠ e := x.1.2
  have hA : (x.1.1 : E) ∈ A := x.2
  simp [indexedBlockEquiv, Equiv.piSplitAt, Equiv.piEquivPiSubtypeProd, hne, hA]

@[simp] lemma indexedBlockEquiv_symm_apply_rest (e : E) (A : Finset E)
    (b : B) (a : AuxiliaryIndex E e A → B) (r : RemainingIndex E e A → B)
    (x : RemainingIndex E e A) :
    (indexedBlockEquiv e A).symm ⟨⟨b, a⟩, r⟩ x.1.1 = r x := by
  have hne : (x.1.1 : E) ≠ e := x.1.2
  have hA : (x.1.1 : E) ∉ A := x.2
  simp [indexedBlockEquiv, Equiv.piSplitAt, Equiv.piEquivPiSubtypeProd, hne, hA]

end PathProduct

namespace PathProduct

open OpenPath Glauber
open JointInvariance

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

/-- The coordinates in a list, viewed as the auxiliary block at `e`. -/
def listAuxiliaryEquiv (e : E) (l : List E) (he : e ∉ l) :
    {f : E // f ∈ l.toFinset} ≃ AuxiliaryIndex E e l.toFinset where
  toFun f := by
    have hne : f.1 ≠ e := by
      intro hfe
      apply he
      have hf : f.1 ∈ l := List.mem_toFinset.mp f.2
      rw [← hfe]
      exact hf
    exact ⟨⟨f.1, hne⟩, f.2⟩
  invFun a := ⟨a.1.1, a.2⟩
  left_inv f := rfl
  right_inv a := rfl

lemma listProd_eq_pi_aux (e : E) (l : List E) (he : e ∉ l)
    (hl : l.Nodup) (ν : E → OpenPath.FinProb B) (t : E → B) :
    (l.map fun f => (ν f).mass (t f)).prod =
      (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset => ν a.1.1)).mass
        (fun a => t a.1.1) := by
  rw [OpenPath.FinProb.pi_mass, ← List.prod_toFinset _ hl]
  rw [Finset.prod_subtype (p := fun x => x ∈ l.toFinset) l.toFinset
    (fun _ => Iff.rfl)]
  exact Fintype.prod_equiv (listAuxiliaryEquiv e l he) _ _ (fun _ => rfl)

lemma agreeOutside_comm {s t : E → B} {l : List E} :
    AgreeOutside s t l ↔ AgreeOutside t s l := by
  constructor <;> intro h f hf
  · exact (h f hf).symm
  · exact (h f hf).symm

lemma indexedBlockEquiv_rest_eq_iff (e : E) (l : List E) (s t : E → B) :
    (indexedBlockEquiv e l.toFinset s).2 =
        (indexedBlockEquiv e l.toFinset t).2 ↔
      AgreeOutside s t (e :: l) := by
  constructor
  · intro h f hf
    have hne : f ≠ e := by
      intro hfe
      subst f
      exact hf (by simp)
    have hnl : f ∉ l.toFinset := by
      simpa using (show f ∉ l from fun hfl => hf (by simp [hfl]))
    let r : RemainingIndex E e l.toFinset := ⟨⟨f, hne⟩, hnl⟩
    have hr := congrFun h r
    simpa [r] using hr
  · intro h
    funext r
    apply h r.1.1
    have hne : (r.1.1 : E) ≠ e := r.1.2
    have hnl : (r.1.1 : E) ∉ l := by simpa using r.2
    simp [hne, hnl]

/-- An edge update followed by off-independent auxiliary refreshes is the
full-refresh block kernel, on the nose rather than merely on a reachable set. -/
theorem sweep_cons_eq_transportedBlockKernel (c : EdgeConditionals B E)
    (ν : E → OpenPath.FinProb B) (l : List E) (e : E)
    (κ : (AuxiliaryIndex E e l.toFinset → B) → OpenPath.FinProb B)
    (he : e ∉ l) (hl : l.Nodup)
    (hc : ∀ f ∈ l, ∀ off, c f off = ν f)
    (hce : ∀ s : E → B, c e (fun f => s f.1) =
      κ (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1)) :
    sweep ((e :: l).map (edgeUpdate c)) =
      transportedBlockKernel (indexedBlockEquiv e l.toFinset)
        (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset => ν a.1.1)) κ := by
  funext s
  apply OpenPath.FinProb.ext
  intro t
  change ((edgeUpdate c e s).bind (sweep (l.map (edgeUpdate c)))).mass t = _
  rw [edgeUpdate_then_sweep_constant_mass c ν e l hl he hc]
  change _ = ((blockKernel
    (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset => ν a.1.1)) κ
    (indexedBlockEquiv e l.toFinset s)).map (indexedBlockEquiv e l.toFinset).symm).mass t
  rw [OpenPath.FinProb.mass_map_equiv]
  simp only [Equiv.symm_symm, blockKernel, OpenPath.FinProb.prod_mass,
    OpenPath.FinProb.pure_mass, indexedBlockEquiv_apply_enhanced,
    indexedBlockEquiv_apply_aux, indexedBlockEquiv_apply_rest]
  rw [hce s, listProd_eq_pi_aux e l he hl]
  have ha : (indexedBlockEquiv e l.toFinset s).1.2 =
      (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1) := by
    funext a
    exact indexedBlockEquiv_apply_aux e l.toFinset s a
  by_cases hst : AgreeOutside s t (e :: l)
  · have hr : (indexedBlockEquiv e l.toFinset t).2 =
        (indexedBlockEquiv e l.toFinset s).2 :=
      (indexedBlockEquiv_rest_eq_iff e l t s).mpr (agreeOutside_comm.mp hst)
    simp [hst, hr, ha]
  · have hr : (indexedBlockEquiv e l.toFinset t).2 ≠
        (indexedBlockEquiv e l.toFinset s).2 := by
      intro hr
      apply hst
      exact agreeOutside_comm.mpr
        ((indexedBlockEquiv_rest_eq_iff e l t s).mp hr)
    simp [hst, hr, ha]

/-- Enhanced-block specialization of `sweep_cons_eq_transportedBlockKernel`. -/
theorem blockUpdate_eq_transportedBlockKernel (c : EdgeConditionals B E)
    (ν : E → OpenPath.FinProb B) (l : List E) (e : E)
    (κ : (AuxiliaryIndex E e l.toFinset → B) → OpenPath.FinProb B)
    (enhanced : Finset E) (heEnhanced : e ∈ enhanced)
    (he : e ∉ l) (hl : l.Nodup)
    (hc : ∀ f ∈ l, ∀ off, c f off = ν f)
    (hce : ∀ s : E → B, c e (fun f => s f.1) =
      κ (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1)) :
    blockUpdate c enhanced l e =
      transportedBlockKernel (indexedBlockEquiv e l.toFinset)
        (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset => ν a.1.1)) κ := by
  unfold blockUpdate blockCoordinates
  rw [if_pos heEnhanced]
  exact sweep_cons_eq_transportedBlockKernel c ν l e κ he hl hc hce

end PathProduct

namespace PathProduct

open OpenPath Glauber
open JointInvariance

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

/-- The mixture equation in `JointProductInvariance` is exactly stationarity of
an actual sequential enhanced block. -/
theorem pi_bind_blockUpdate_invariant (ν : E → OpenPath.FinProb B)
    (c : EdgeConditionals B E) (l : List E) (e : E)
    (κ : (AuxiliaryIndex E e l.toFinset → B) → OpenPath.FinProb B)
    (enhanced : Finset E) (heEnhanced : e ∈ enhanced)
    (he : e ∉ l) (hl : l.Nodup)
    (hc : ∀ f ∈ l, ∀ off, c f off = ν f)
    (hce : ∀ s : E → B, c e (fun f => s f.1) =
      κ (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1))
    (hκ : (OpenPath.FinProb.pi
      (fun a : AuxiliaryIndex E e l.toFinset => ν a.1.1)).bind κ = ν e) :
    (OpenPath.FinProb.pi ν).bind (blockUpdate c enhanced l e) =
      OpenPath.FinProb.pi ν := by
  rw [blockUpdate_eq_transportedBlockKernel c ν l e κ enhanced heEnhanced he hl hc hce]
  exact pi_bind_transportedBlockKernel_invariant ν e l.toFinset κ hκ

end PathProduct

namespace PathProduct

open OpenPath Glauber
open JointInvariance

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

theorem pi_bind_empty_auxiliary (ν : E → OpenPath.FinProb B) (e : E) :
    (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e ([] : List E).toFinset => ν a.1.1)).bind
      (fun _ => ν e) = ν e := by
  apply OpenPath.FinProb.ext
  intro b
  change (∑ a, (OpenPath.FinProb.pi
    (fun a : AuxiliaryIndex E e ([] : List E).toFinset => ν a.1.1)).mass a *
      (ν e).mass b) = (ν e).mass b
  rw [← Finset.sum_mul, (OpenPath.FinProb.pi
    (fun a : AuxiliaryIndex E e ([] : List E).toFinset => ν a.1.1)).sum_mass, one_mul]

/-- A product law is invariant under an off-independent single-coordinate
refresh. This is the empty-auxiliary case of the block theorem. -/
theorem pi_bind_edgeUpdate_invariant_of_constant
    (ν : E → OpenPath.FinProb B) (c : EdgeConditionals B E) (e : E)
    (hc : ∀ off, c e off = ν e) :
    (OpenPath.FinProb.pi ν).bind (edgeUpdate c e) = OpenPath.FinProb.pi ν := by
  let κ : (AuxiliaryIndex E e ([] : List E).toFinset → B) → OpenPath.FinProb B :=
    fun _ => ν e
  have hce : ∀ s : E → B, c e (fun f => s f.1) =
      κ (fun a : AuxiliaryIndex E e ([] : List E).toFinset => s a.1.1) := by
    intro s
    exact hc _
  have hκ : (OpenPath.FinProb.pi
      (fun a : AuxiliaryIndex E e ([] : List E).toFinset => ν a.1.1)).bind κ = ν e :=
    pi_bind_empty_auxiliary ν e
  have h := pi_bind_blockUpdate_invariant ν c [] e κ {e} (by simp)
    (by simp) (by simp) (by simp) hce hκ
  have hk : blockUpdate c {e} [] e = edgeUpdate c e := by
    funext s
    simp [blockUpdate, blockCoordinates, sweep, Glauber.seq,
      Glauber.FinProb.bind_dirac_right]
  rw [hk] at h
  exact h

end PathProduct
