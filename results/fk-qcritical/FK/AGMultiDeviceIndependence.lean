import FK.AGSleeveDifferential
import FK.AGUniformSleevePacking

/-!
# Sleeves with independent, separately indexed activations

The existing `AGSleevedAnnulus` construction uses one `Unit` activation for a
whole sleeve. This module retains that construction and gives each member of
an indexed family its own activation coordinate. The coordinate laws are an
actual `FinProb.pi` product. No infinite-volume assertion is made.
-/

open Set
open scoped Classical BigOperators Sym2

namespace FK.AGImplant.Sleeve

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation

universe u v w

/-- A family of sleeves with one independent activation coordinate per index. -/
noncomputable def independentSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) : ι → Set (graph H).edgeSet :=
  fun i => ↑(edges H (S i))

@[simp] lemma mem_independentSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (i : ι)
    {f : (graph H).edgeSet} :
    f ∈ independentSupport H S i ↔ f ∈ edges H (S i) := Iff.rfl

/-- Opening activation `i` repairs precisely the `i`-th selected annulus. -/
lemma independent_open_bypass {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (i : ι) {e : H.edgeSet} (he : e ∈ S i)
    (χ : JointConfig (graph H).edgeSet ι) :
    OpenConnected (graph H)
      (deviceConfig (independentSupport H S)
        (forceEdge (annularClose (annulus H (S i)) χ) (Sum.inr i) true))
      Set.univ (Sum.inl (e : Sym2 V).out.1) (Sum.inl (e : Sym2 V).out.2) := by
  have hleft : deviceConfig (independentSupport H S)
      (forceEdge (annularClose (annulus H (S i)) χ) (Sum.inr i) true)
      (leftSpoke H e) = true := by
    apply deviceConfig_eq_true_of_mem (independentSupport H S) _ i (leftSpoke H e)
    · exact forceEdge_same _ _ _
    · exact leftSpoke_mem_edges H (S i) he
  have hright : deviceConfig (independentSupport H S)
      (forceEdge (annularClose (annulus H (S i)) χ) (Sum.inr i) true)
      (rightSpoke H e) = true := by
    apply deviceConfig_eq_true_of_mem (independentSupport H S) _ i (rightSpoke H e)
    · exact forceEdge_same _ _ _
    · exact rightSpoke_mem_edges H (S i) he
  have hleftAdj : (graph H).Adj
      (Sum.inl (e : Sym2 V).out.1) (Sum.inr e) := Sym2.out_fst_mem (e : Sym2 V)
  have hrightAdj : (graph H).Adj
      (Sum.inr e) (Sum.inl (e : Sym2 V).out.2) := Sym2.out_snd_mem (e : Sym2 V)
  apply (OpenConnected.of_adj hleftAdj (Set.mem_univ _) ?_).trans
  · apply OpenConnected.of_adj hrightAdj (Set.mem_univ _)
    exact hright
  · exact hleft

/-- Actual two-edge replacement walks for every bond in the `i`-th annulus. -/
lemma independent_annular_replacement {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (i : ι)
    {χ : JointConfig (graph H).edgeSet ι} {x y : V ⊕ H.edgeSet}
    (hxy : (graph H).Adj x y)
    (hf : (⟨s(x, y), hxy⟩ : (graph H).edgeSet) ∈ annulus H (S i)) :
    OpenConnected (graph H)
      (deviceConfig (independentSupport H S)
        (forceEdge (annularClose (annulus H (S i)) χ) (Sum.inr i) true))
      Set.univ x y := by
  obtain ⟨e, he, hef⟩ := mem_annulus H (S := S i)
    (f := ⟨s(x, y), hxy⟩) |>.mp hf
  have hval := congrArg Subtype.val hef
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2) =
    s(x, y) at hval
  rcases Sym2.eq_iff.mp hval with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · cases hx
    cases hy
    exact independent_open_bypass H S i he χ
  · cases hx
    cases hy
    exact openConnected_reverse (independent_open_bypass H S i he χ)

/-- A selected bond pivot becomes a pivot of its own activation, not of a
single activation shared by all devices. -/
theorem activationPivotal_deviceArmEvent_independent {V : Type u}
    (H : SimpleGraph V) {ι : Type v} (S : ι → Finset H.edgeSet) (i : ι)
    {e : H.edgeSet} (he : e ∈ S i) {o : V ⊕ H.edgeSet} (n : ℕ)
    {χ : JointConfig (graph H).edgeSet ι}
    (hpiv : EdgePivotal
      (deviceArmEvent (graph H) (independentSupport H S) o n)
      (baseEdge H e) χ) :
    ActivationPivotal
      (deviceArmEvent (graph H) (independentSupport H S) o n) i
      (annularClose (annulus H (S i)) χ) := by
  classical
  rw [← baseEdge_eq H e (baseEdge_adj H e)] at hpiv
  apply activationPivotal_deviceArmEvent_annularClose (baseEdge_adj H e)
    (annulus H (S i)) (by
      have hm := baseEdge_mem_annulus H (S i) he
      rwa [← baseEdge_eq H e (baseEdge_adj H e)] at hm)
    (independentSupport H S) i n
  intro ξ x y hxy hf
  exact independent_annular_replacement H S i y hf
  exact hpiv

/-- The open-connection version of the separate-activation conversion. -/
theorem activationPivotal_openConnected_independent {V : Type u}
    (H : SimpleGraph V) {ι : Type v} (S : ι → Finset H.edgeSet) (i : ι)
    {e : H.edgeSet} (he : e ∈ S i) {a b : V ⊕ H.edgeSet}
    {χ : JointConfig (graph H).edgeSet ι}
    (hpiv : EdgePivotal
      (deviceEvent (independentSupport H S)
        {ω | OpenConnected (graph H) ω Set.univ a b}) (baseEdge H e) χ) :
    ActivationPivotal
      (deviceEvent (independentSupport H S)
        {ω | OpenConnected (graph H) ω Set.univ a b}) i
      (annularClose (annulus H (S i)) χ) := by
  classical
  rw [← baseEdge_eq H e (baseEdge_adj H e)] at hpiv
  apply activationPivotal_openConnected_annularClose (baseEdge_adj H e)
    (annulus H (S i)) (by
      have hm := baseEdge_mem_annulus H (S i) he
      rwa [← baseEdge_eq H e (baseEdge_adj H e)] at hm)
    (independentSupport H S) i
  intro ξ x y hxy hf
  exact independent_annular_replacement H S i y hf
  exact hpiv

/-- Exact normalized product-law comparison for one member of the family. -/
theorem deviceArmEvent_independent_edgePivotal_event_mul_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (bond : (graph H).edgeSet → OpenPath.FinProb Bool)
    (activation : ι → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (S : ι → Finset H.edgeSet) (i : ι) {e : H.edgeSet} (he : e ∈ S i)
    {o : V ⊕ H.edgeSet} (n : ℕ) :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ (S i).card * μ.event {χ | EdgePivotal
      (deviceArmEvent (graph H) (independentSupport H S) o n)
      (baseEdge H e) χ} ≤
    ((2 ^ (S i).card : ℕ) : ℝ) * μ.event {χ | ActivationPivotal
      (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
  classical
  dsimp only
  have hm : (⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2),
      baseEdge_adj H e⟩ : (graph H).edgeSet) ∈ annulus H (S i) := by
    rw [baseEdge_eq H e (baseEdge_adj H e)]
    exact baseEdge_mem_annulus H (S i) he
  have h := deviceArmEvent_annular_edgePivotal_event_mul_le (o := o)
    bond activation δ hδ hbond hactivation (baseEdge_adj H e)
    (annulus H (S i)) hm (independentSupport H S) i n (by
      intro ξ x y hxy hopen hf
      exact independent_annular_replacement H S i hxy hf)
  rw [baseEdge_eq H e (baseEdge_adj H e)] at h
  simpa only [card_annulus] using h

/-- Within device `i`, its selected bond sum is controlled by its own
activation-pivot probability. -/
theorem deviceArmEvent_independent_sum_edgePivotal_event_mul_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (bond : (graph H).edgeSet → OpenPath.FinProb Bool)
    (activation : ι → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (S : ι → Finset H.edgeSet) (i : ι) {o : V ⊕ H.edgeSet} (n : ℕ) :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ (S i).card * (∑ e ∈ S i, μ.event {χ | EdgePivotal
      (deviceArmEvent (graph H) (independentSupport H S) o n)
      (baseEdge H e) χ}) ≤
    ((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ) *
      μ.event {χ | ActivationPivotal
        (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
  classical
  dsimp only
  calc
    δ ^ (S i).card * (∑ e ∈ S i,
        (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
          EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n)
            (baseEdge H e) χ}) =
        ∑ e ∈ S i, δ ^ (S i).card *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n)
              (baseEdge H e) χ} := by rw [Finset.mul_sum]
    _ ≤ ∑ _e ∈ S i, ((2 ^ (S i).card : ℕ) : ℝ) *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal
              (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
      apply Finset.sum_le_sum
      intro e he
      exact deviceArmEvent_independent_edgePivotal_event_mul_le H bond activation
        δ hδ hbond hactivation S i he n
    _ = ((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ) *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal
              (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Splitting a joint configuration exposes the product of the bond law and
the genuinely indexed activation law. -/
theorem pi_map_jointSplit {E : Type u} {ι : Type v}
    [Fintype E] [DecidableEq E] [Fintype ι] [DecidableEq ι]
    (bond : E → OpenPath.FinProb Bool) (activation : ι → OpenPath.FinProb Bool) :
    (OpenPath.FinProb.pi (Sum.elim bond activation)).map
      (Equiv.sumArrowEquivProdArrow E ι Bool) =
      (OpenPath.FinProb.pi bond).prod (OpenPath.FinProb.pi activation) := by
  apply OpenPath.FinProb.ext
  intro χ
  rw [OpenPath.FinProb.mass_map_equiv]
  simp only [OpenPath.FinProb.pi_mass, Fintype.prod_sum_type,
    OpenPath.FinProb.prod_mass, Equiv.sumArrowEquivProdArrow,
    Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr]

/-- The marginal on all activation coordinates is exactly their indexed
independent product, with every bond coordinate summed out. -/
theorem pi_map_activations {E : Type u} {ι : Type v}
    [Fintype E] [DecidableEq E] [Fintype ι] [DecidableEq ι]
    (bond : E → OpenPath.FinProb Bool) (activation : ι → OpenPath.FinProb Bool) :
    (OpenPath.FinProb.pi (Sum.elim bond activation)).map
      (fun χ i => χ (Sum.inr i)) = OpenPath.FinProb.pi activation := by
  calc
    (OpenPath.FinProb.pi (Sum.elim bond activation)).map
        (fun χ i => χ (Sum.inr i)) =
        ((OpenPath.FinProb.pi (Sum.elim bond activation)).map
          (Equiv.sumArrowEquivProdArrow E ι Bool)).map Prod.snd := by
      rw [GlauberCoupling.map_map]
      rfl
    _ = (OpenPath.FinProb.pi activation) := by
      rw [pi_map_jointSplit, OpenPath.FinProb.prod_map_snd]

/-- An entire prescribed activation profile has the product of its individual
coordinate masses; this is not a shared-activation probability. -/
theorem activationProfile_marginal_mass {E : Type u} {ι : Type v}
    [Fintype E] [DecidableEq E] [Fintype ι] [DecidableEq ι]
    (bond : E → OpenPath.FinProb Bool) (activation : ι → OpenPath.FinProb Bool)
    (α : ι → Bool) :
    ((OpenPath.FinProb.pi (Sum.elim bond activation)).map
      (fun χ i => χ (Sum.inr i))).mass α = ∏ i, (activation i).mass (α i) := by
  rw [pi_map_activations, OpenPath.FinProb.pi_mass]

/-- Every activation-only event has exactly the probability assigned by the
indexed activation product after summing out all ordinary bonds. -/
theorem activationEvent_marginal {E : Type u} {ι : Type v}
    [Fintype E] [DecidableEq E] [Fintype ι] [DecidableEq ι]
    (bond : E → OpenPath.FinProb Bool) (activation : ι → OpenPath.FinProb Bool)
    (C : Set (ι → Bool)) :
    (OpenPath.FinProb.pi (Sum.elim bond activation)).event
      ((fun χ i => χ (Sum.inr i)) ⁻¹' C) =
        (OpenPath.FinProb.pi activation).event C := by
  rw [OpenPath.FinProb.event_preimage_map, pi_map_activations]

/-- Exact joint point mass, displayed as separate bond and activation products. -/
theorem independent_joint_mass {E : Type u} {ι : Type v}
    [Fintype E] [DecidableEq E] [Fintype ι] [DecidableEq ι]
    (bond : E → OpenPath.FinProb Bool) (activation : ι → OpenPath.FinProb Bool)
    (χ : JointConfig E ι) :
    (OpenPath.FinProb.pi (Sum.elim bond activation)).mass χ =
      (∏ e, (bond e).mass (χ (Sum.inl e))) *
        ∏ i, (activation i).mass (χ (Sum.inr i)) := by
  simp only [OpenPath.FinProb.pi_mass, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]

/-- For equal annulus sizes, the full finite family has one exact summed pivot
comparison. The right side sums distinct activation coordinates. -/
theorem deviceArmEvent_independent_total_edgePivotal_event_mul_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (bond : (graph H).edgeSet → OpenPath.FinProb Bool)
    (activation : ι → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (S : ι → Finset H.edgeSet) (R : ℕ) (hcard : ∀ i, (S i).card = R)
    {o : V ⊕ H.edgeSet} (n : ℕ) :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ R * (∑ i, ∑ e ∈ S i, μ.event {χ | EdgePivotal
      (deviceArmEvent (graph H) (independentSupport H S) o n)
      (baseEdge H e) χ}) ≤
    (((2 ^ R : ℕ) : ℝ) * (R : ℝ)) * ∑ i, μ.event {χ | ActivationPivotal
      (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
  classical
  dsimp only
  calc
    δ ^ R * (∑ i, ∑ e ∈ S i,
        (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
          EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n)
            (baseEdge H e) χ}) =
        ∑ i, δ ^ (S i).card * (∑ e ∈ S i,
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n)
              (baseEdge H e) χ}) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcard i]
    _ ≤ ∑ i, (((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ)) *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal
              (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
      apply Finset.sum_le_sum
      intro i hi
      exact deviceArmEvent_independent_sum_edgePivotal_event_mul_le H bond
        activation δ hδ hbond hactivation S i n
    _ = (((2 ^ R : ℕ) : ℝ) * (R : ℝ)) * ∑ i,
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal
              (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcard i]

/-- The ordinary base bonds moved for an indexed finite family. -/
noncomputable def independentBaseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) : Finset (graph H).edgeSet := by
  classical
  exact Finset.univ.biUnion fun i => annulus H (S i)

@[simp] lemma mem_independentBaseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    {S : ι → Finset H.edgeSet} {f : (graph H).edgeSet} :
    f ∈ independentBaseSupport H S ↔ ∃ i, f ∈ annulus H (S i) := by
  classical
  simp [independentBaseSupport]

/-- Independent activation velocities: every device has its own `+1`
coordinate, while selected base bonds have velocity `-c`. -/
noncomputable def independentVelocity {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) (c : ℝ) : (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if e ∈ independentBaseSupport H S then -c else 0) (fun _ => 1)

lemma sum_independentVelocity_mul {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) (c : ℝ) (W : (graph H).edgeSet ⊕ ι → ℝ) :
    (∑ x, independentVelocity H S c x * W x) =
      (-c) * (∑ e ∈ independentBaseSupport H S, W (Sum.inl e)) +
        ∑ i, W (Sum.inr i) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [independentVelocity, Sum.elim_inl, Sum.elim_inr, one_mul]
  congr 1
  calc
    (∑ e : (graph H).edgeSet,
        (if e ∈ independentBaseSupport H S then -c else 0) * W (Sum.inl e)) =
        ∑ e ∈ independentBaseSupport H S,
          (if e ∈ independentBaseSupport H S then -c else 0) * W (Sum.inl e) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e he heS
      simp [heS]
    _ = ∑ e ∈ independentBaseSupport H S, (-c) * W (Sum.inl e) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [he]
    _ = (-c) * (∑ e ∈ independentBaseSupport H S, W (Sum.inl e)) := by
      rw [Finset.mul_sum]

/-- On pairwise-disjoint annuli, the union sum is exactly the double sum
over device indices and their original bonds. -/
lemma sum_independentBaseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (W : (graph H).edgeSet → ℝ) :
    (∑ f ∈ independentBaseSupport H S, W f) =
      ∑ i, ∑ e ∈ S i, W (baseEdge H e) := by
  classical
  rw [independentBaseSupport, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i hi
    have himage : annulus H (S i) = (S i).image (baseEdge H) := by
      ext f
      simp [annulus]
    rw [himage]
    exact Finset.sum_image (baseEdge_injective H).injOn
  · intro i hi j hj hij
    exact hdisj i j hij

/-- Exact ordinary-bond support size for disjoint annuli. -/
lemma card_independentBaseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j))) :
    (independentBaseSupport H S).card = ∑ i, (S i).card := by
  classical
  rw [independentBaseSupport, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i hi
    exact card_annulus H (S i)
  · intro i hi j hj hij
    exact hdisj i j hij

/-- Uniform support constant: `|ι| * R` moved base bonds and exactly `|ι|`
independent activation coordinates. -/
lemma card_independentBaseSupport_uniform {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hcard : ∀ i, (S i).card = R) :
    (independentBaseSupport H S).card = Fintype.card ι * R := by
  rw [card_independentBaseSupport H S hdisj]
  simp [hcard, mul_comm]

/-- Affine comparison line for all activations simultaneously. -/
noncomputable def independentSleeveLine {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) (p s c t : ℝ) : (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if e ∈ independentBaseSupport H S then p - c * t else p)
    (fun _ => s + t)

lemma independentSleeveLine_eq_affine {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) (p s c t : ℝ) :
    independentSleeveLine H S p s c t =
      affineRates (independentSleeveLine H S p s c 0)
        (independentVelocity H S c) t := by
  classical
  funext x
  cases x with
  | inl e =>
      by_cases he : e ∈ independentBaseSupport H S
      · change (if e ∈ independentBaseSupport H S then p - c * t else p) =
          (if e ∈ independentBaseSupport H S then p - c * 0 else p) +
            t * (if e ∈ independentBaseSupport H S then -c else 0)
        simp only [he, ↓reduceIte]
        ring
      · change (if e ∈ independentBaseSupport H S then p - c * t else p) =
          (if e ∈ independentBaseSupport H S then p - c * 0 else p) +
            t * (if e ∈ independentBaseSupport H S then -c else 0)
        simp only [he, ↓reduceIte]
        ring
  | inr i =>
      simp only [independentSleeveLine, independentVelocity, affineRates,
        Sum.elim_inr, mul_one, add_zero]

/-- The affine finite derivative has one activation-pivot term per device,
not a single pivot term repeated by the number of selected bonds. -/
theorem hasDerivAt_eventWeight_independentSleeveLine_pivotal {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (p s c : ℝ) {A : Set (JointConfig (graph H).edgeSet ι)}
    (hA : IsUpperSet A) (t : ℝ) :
    HasDerivAt (fun y => eventWeight (independentSleeveLine H S p s c y) A)
      ((-c) * (∑ i, ∑ e ∈ S i, eventWeight (independentSleeveLine H S p s c t)
        {χ | EdgePivotal A (baseEdge H e) χ}) +
        ∑ i, eventWeight (independentSleeveLine H S p s c t)
          {χ | ActivationPivotal A i χ}) t := by
  classical
  have hfun : (fun y => eventWeight (independentSleeveLine H S p s c y) A) =
      (fun y => eventWeight (affineRates (independentSleeveLine H S p s c 0)
        (independentVelocity H S c) y) A) := by
    funext y
    rw [independentSleeveLine_eq_affine]
  have h := hasDerivAt_eventWeight_affine_pivotal
    (independentSleeveLine H S p s c 0) (independentVelocity H S c) hA t
  rw [sum_independentVelocity_mul] at h
  rw [← hfun] at h
  rw [← independentSleeveLine_eq_affine H S p s c t] at h
  have hbase := sum_independentBaseSupport H S hdisj
    (fun f => eventWeight (independentSleeveLine H S p s c t)
      {χ | Pivotal A (Sum.inl f) χ})
  rw [hbase] at h
  exact h

/-- Common normalized speed for `R` simultaneous repairs per independent
activation. -/
noncomputable def independentComparisonSpeed (a b : ℝ) (R : ℕ) : ℝ :=
  (sleeveMinorant a b) ^ R / (((2 ^ R : ℕ) : ℝ) * (R : ℝ))

lemma independentComparisonSpeed_pos {a b : ℝ} {R : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hb : b < 1) :
    0 < independentComparisonSpeed a b R := by
  apply div_pos (pow_pos (sleeveMinorant_pos ha hb) _)
  have hcard : 0 < (R : ℝ) := by exact_mod_cast hR
  positivity

lemma independentComparisonSpeed_nonneg {a b : ℝ} (R : ℕ)
    (ha : 0 ≤ a) (hb : b ≤ 1) : 0 ≤ independentComparisonSpeed a b R := by
  apply div_nonneg (pow_nonneg (sleeveMinorant_nonneg ha hb) _)
  positivity

lemma independentSleeveLine_mem_box {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) {p s c t a b : ℝ}
    (hp : p ∈ Icc a b) (hmove : p - c * t ∈ Icc a b) (hs : s + t ∈ Icc a b)
    (x : (graph H).edgeSet ⊕ ι) : independentSleeveLine H S p s c t x ∈ Icc a b := by
  cases x with
  | inl e =>
      by_cases he : e ∈ independentBaseSupport H S
      · change (if e ∈ independentBaseSupport H S then p - c * t else p) ∈ Icc a b
        simp only [he, ↓reduceIte]
        exact hmove
      · change (if e ∈ independentBaseSupport H S then p - c * t else p) ∈ Icc a b
        simp only [he, ↓reduceIte]
        exact hp
  | inr i => exact hs

/-- On the unit cube, the multi-device polynomial is exactly the normalized
independent product law with separately indexed activation coordinates. -/
lemma eventWeight_independentSleeveLine_eq_pi {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] [Fintype (graph H).edgeSet]
    [DecidableEq ι] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, independentSleeveLine H S p s c t x ∈ Icc (0 : ℝ) 1)
    (A : Set (JointConfig (graph H).edgeSet ι)) :
    eventWeight (independentSleeveLine H S p s c t) A =
      (OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw (independentSleeveLine H S p s c t (Sum.inl e))
          (hr (Sum.inl e)))
        (fun i => boolLaw (independentSleeveLine H S p s c t (Sum.inr i))
          (hr (Sum.inr i))))).event A := by
  have hlaw : boolProduct (independentSleeveLine H S p s c t) hr =
      OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw (independentSleeveLine H S p s c t (Sum.inl e))
          (hr (Sum.inl e)))
        (fun i => boolLaw (independentSleeveLine H S p s c t (Sum.inr i))
          (hr (Sum.inr i)))) := by
    unfold boolProduct
    congr 1
    funext x
    cases x <;> rfl
  rw [eventWeight_eq_boolProduct_event (independentSleeveLine H S p s c t) hr, hlaw]

/-- Normalized multi-device differential comparison.  Every device supplies
one independently activated pivot probability, with the same exact speed per
`R`-bond annulus. -/
lemma deviceArmEvent_independentPivotSlope_nonneg_of_box {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b t : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp : p ∈ Icc a b)
    (hmove : p - independentComparisonSpeed a b R * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) :
    let c := independentComparisonSpeed a b R
    0 ≤ (-c) * (∑ i, ∑ e ∈ S i, eventWeight (independentSleeveLine H S p s c t)
      {χ | EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n)
        (baseEdge H e) χ}) +
      ∑ i, eventWeight (independentSleeveLine H S p s c t)
        {χ | ActivationPivotal
          (deviceArmEvent (graph H) (independentSupport H S) o n) i χ} := by
  classical
  dsimp only
  let c := independentComparisonSpeed a b R
  let r := independentSleeveLine H S p s c t
  let Dp : ι → ℝ := fun i => ∑ e ∈ S i, eventWeight r
    {χ | EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n)
      (baseEdge H e) χ}
  let Pa : ι → ℝ := fun i => eventWeight r {χ | ActivationPivotal
    (deviceArmEvent (graph H) (independentSupport H S) o n) i χ}
  let den : ℝ := ((2 ^ R : ℕ) : ℝ) * (R : ℝ)
  have hrbox : ∀ x, r x ∈ Icc a b := by
    intro x
    exact independentSleeveLine_mem_box H S hp hmove hs x
  have hr : ∀ x, r x ∈ Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨ha.le.trans (hrbox x).1, (hrbox x).2.trans hb.le⟩
  let bond := fun e => boolLaw (r (Sum.inl e)) (hr (Sum.inl e))
  let activation := fun i => boolLaw (r (Sum.inr i)) (hr (Sum.inr i))
  have hminor : 0 < sleeveMinorant a b := sleeveMinorant_pos ha hb
  have hbond : ∀ e bit, sleeveMinorant a b ≤ (bond e).mass bit := by
    intro e bit
    exact sleeveMinorant_le_boolLaw (hrbox (Sum.inl e)) (hr (Sum.inl e)) bit
  have hactivation : ∀ i bit, sleeveMinorant a b ≤ (activation i).mass bit := by
    intro i bit
    exact sleeveMinorant_le_boolLaw (hrbox (Sum.inr i)) (hr (Sum.inr i)) bit
  have hevent (C : Set (JointConfig (graph H).edgeSet ι)) :
      (OpenPath.FinProb.pi (Sum.elim bond activation)).event C = eventWeight r C := by
    simpa only [bond, activation, r] using
      (eventWeight_independentSleeveLine_eq_pi H S p s c t hr C).symm
  have hsum (i : ι) : (sleeveMinorant a b) ^ R * Dp i ≤ den * Pa i := by
    have h := deviceArmEvent_independent_sum_edgePivotal_event_mul_le H bond
      activation (sleeveMinorant a b) hminor.le hbond hactivation S i n (o := o)
    dsimp only at h
    simp_rw [hevent] at h
    change (sleeveMinorant a b) ^ (S i).card * Dp i ≤
      (((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ)) * Pa i at h
    rw [hcard i] at h
    exact h
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hden0 : den ≠ 0 := ne_of_gt hden
  have hcδ : c * den = (sleeveMinorant a b) ^ R := by
    change ((sleeveMinorant a b) ^ R / den) * den = (sleeveMinorant a b) ^ R
    exact div_mul_cancel₀ _ hden0
  have hmul (i : ι) : c * Dp i ≤ Pa i := by
    refine le_of_mul_le_mul_right (a := den) ?_ hden
    calc
      (c * Dp i) * den = (c * den) * Dp i := by ring
      _ = (sleeveMinorant a b) ^ R * Dp i := by rw [hcδ]
      _ ≤ den * Pa i := hsum i
      _ = Pa i * den := by ring
  have htotal : c * (∑ i, Dp i) ≤ ∑ i, Pa i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hmul i
  change 0 ≤ (-c) * (∑ i, Dp i) + ∑ i, Pa i
  linarith

/-- Endpoint parameters bound every intermediate point of the indexed line. -/
lemma independentSleeveLine_parameters_mem_box {p s c a b T t : ℝ}
    (hc : 0 ≤ c) (ht : t ∈ Icc (0 : ℝ) T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - c * T ∈ Icc a b) (hsT : s + T ∈ Icc a b) :
    p - c * t ∈ Icc a b ∧ s + t ∈ Icc a b :=
  FK.AGGadget.diagonal_parameters_mem_Icc hc ht hp0 hs0 hpT hsT

/-- Monotonicity of the finite comparison curve with all indexed activations
increasing independently and all selected bonds decreasing. -/
theorem monotoneOn_deviceArmEvent_independentSleeveLine {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    MonotoneOn (fun t => eventWeight
      (independentSleeveLine H S p s (independentComparisonSpeed a b R) t)
      (deviceArmEvent (graph H) (independentSupport H S) o n)) (Icc (0 : ℝ) T) := by
  classical
  let c := independentComparisonSpeed a b R
  let Dp : ℝ → ℝ := fun t => ∑ i, ∑ e ∈ S i,
    eventWeight (independentSleeveLine H S p s c t)
      {χ | EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n)
        (baseEdge H e) χ}
  let Pa : ℝ → ℝ := fun t => ∑ i, eventWeight (independentSleeveLine H S p s c t)
    {χ | ActivationPivotal (deviceArmEvent (graph H) (independentSupport H S) o n) i χ}
  have hc : 0 ≤ c := independentComparisonSpeed_nonneg R ha.le hb.le
  have hderiv (t : ℝ) :
      HasDerivAt (fun y => eventWeight (independentSleeveLine H S p s c y)
        (deviceArmEvent (graph H) (independentSupport H S) o n))
        ((-c) * Dp t + Pa t) t := by
    exact hasDerivAt_eventWeight_independentSleeveLine_pivotal H S hdisj p s c
      (isUpperSet_deviceArmEvent (graph H) (independentSupport H S) o n) t
  change MonotoneOn (fun t => eventWeight (independentSleeveLine H S p s c t)
    (deviceArmEvent (graph H) (independentSupport H S) o n)) (Icc (0 : ℝ) T)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T)
    (f' := fun t => (-c) * Dp t + Pa t)
  · intro t ht
    exact (hderiv t).continuousAt.continuousWithinAt
  · intro t ht
    exact (hderiv t).hasDerivWithinAt
  · intro t ht
    have htcc : t ∈ Icc (0 : ℝ) T := interior_subset ht
    have hbox := independentSleeveLine_parameters_mem_box hc htcc hp0 hs0 hpT hsT
    exact deviceArmEvent_independentPivotSlope_nonneg_of_box H S R hR hcard o n
      p s a b t ha hb hp0 hbox.1 hbox.2

/-- Endpoint comparison on the product-polynomial probability. -/
theorem deviceArmEventWeight_independentSleeveLine_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    eventWeight (independentSleeveLine H S p s (independentComparisonSpeed a b R) 0)
        (deviceArmEvent (graph H) (independentSupport H S) o n) ≤
      eventWeight (independentSleeveLine H S p s (independentComparisonSpeed a b R) T)
        (deviceArmEvent (graph H) (independentSupport H S) o n) := by
  have hmono := monotoneOn_deviceArmEvent_independentSleeveLine H S hdisj R hR
    hcard o n p s a b T ha hb hp0 hs0 hpT hsT
  exact hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

/-- The endpoint comparison for the actual normalized independent product
laws, retaining the separate activation coordinate at every device. -/
theorem deviceArmEvent_productLaw_independentSleeveLine_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, independentSleeveLine H S p s (independentComparisonSpeed a b R) 0 x ∈
      Icc (0 : ℝ) 1)
    (hrT : ∀ x, independentSleeveLine H S p s (independentComparisonSpeed a b R) T x ∈
      Icc (0 : ℝ) 1) :
    (OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw (independentSleeveLine H S p s
          (independentComparisonSpeed a b R) 0 (Sum.inl e)) (hr0 (Sum.inl e)))
        (fun i => boolLaw (independentSleeveLine H S p s
          (independentComparisonSpeed a b R) 0 (Sum.inr i)) (hr0 (Sum.inr i))))).event
        (deviceArmEvent (graph H) (independentSupport H S) o n) ≤
      (OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw (independentSleeveLine H S p s
          (independentComparisonSpeed a b R) T (Sum.inl e)) (hrT (Sum.inl e)))
        (fun i => boolLaw (independentSleeveLine H S p s
          (independentComparisonSpeed a b R) T (Sum.inr i)) (hrT (Sum.inr i))))).event
        (deviceArmEvent (graph H) (independentSupport H S) o n) := by
  rw [← eventWeight_independentSleeveLine_eq_pi H S p s
      (independentComparisonSpeed a b R) 0 hr0,
    ← eventWeight_independentSleeveLine_eq_pi H S p s
      (independentComparisonSpeed a b R) T hrT]
  exact deviceArmEventWeight_independentSleeveLine_le H S hdisj R hR hcard o n
    p s a b T ha hb hT hp0 hs0 hpT hsT

/-- Disjoint complete templates give disjoint annuli and disjoint activation
edge sets. -/
lemma disjoint_annulus_of_disjoint_template {V : Type u} (H : SimpleGraph V)
    {S T : Finset H.edgeSet} (h : Disjoint (template H S) (template H T)) :
    Disjoint (annulus H S) (annulus H T) := by
  classical
  rw [Finset.disjoint_left] at h ⊢
  intro f hfS hfT
  exact h ((mem_template H).mpr (Or.inl hfS)) ((mem_template H).mpr (Or.inl hfT))

lemma disjoint_edges_of_disjoint_template {V : Type u} (H : SimpleGraph V)
    {S T : Finset H.edgeSet} (h : Disjoint (template H S) (template H T)) :
    Disjoint (edges H S) (edges H T) := by
  classical
  rw [Finset.disjoint_left] at h ⊢
  intro f hfS hfT
  exact h ((mem_template H).mpr (Or.inr hfS)) ((mem_template H).mpr (Or.inr hfT))

/-- The actual uniform sleeve packing supplies the disjointness input to the
independent differential theorem; it is not postulated separately. -/
theorem disjoint_packedAnnuli {V : Type u} (H : SimpleGraph V)
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    {φ ψ : H ≃g H} (hφ : φ ∈ M) (hψ : ψ ∈ M) (hne : φ ≠ ψ) :
    Disjoint (annulus H (S.map φ.mapEdgeSet.toEmbedding))
      (annulus H (S.map ψ.mapEdgeSet.toEmbedding)) := by
  apply disjoint_annulus_of_disjoint_template H
  exact pairwiseDisjoint_packedTemplates H S hM hφ hψ hne

/-- Disjoint activation supports of two distinct packed sleeves. -/
theorem disjoint_packedIndependentSupport {V : Type u} (H : SimpleGraph V)
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    {φ ψ : H ≃g H} (hφ : φ ∈ M) (hψ : ψ ∈ M) (hne : φ ≠ ψ) :
    Disjoint (edges H (S.map φ.mapEdgeSet.toEmbedding))
      (edges H (S.map ψ.mapEdgeSet.toEmbedding)) := by
  apply disjoint_edges_of_disjoint_template H
  exact pairwiseDisjoint_packedTemplates H S hM hφ hψ hne

/-- The finite-subtype form needed directly by the indexed derivative. -/
theorem disjoint_packedIndependentAnnuli_fintype {V : Type u} (H : SimpleGraph V)
    [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M) :
    ∀ φ ψ : {φ // φ ∈ F}, φ ≠ ψ →
      Disjoint (annulus H (S.map φ.1.mapEdgeSet.toEmbedding))
        (annulus H (S.map ψ.1.mapEdgeSet.toEmbedding)) := by
  intro φ ψ hne
  apply disjoint_packedAnnuli H S hM (hFM φ.2) (hFM ψ.2)
  intro heq
  exact hne (Subtype.ext heq)

/-- Exact no-overlap accounting for the activation coordinates' edge supports
in any finite part of the actual packing. -/
theorem card_biUnion_packedIndependentSupports {V : Type u} (H : SimpleGraph V)
    [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M) :
    (F.biUnion fun φ => edges H (S.map φ.mapEdgeSet.toEmbedding)).card =
      ∑ φ ∈ F, (edges H (S.map φ.mapEdgeSet.toEmbedding)).card := by
  classical
  apply Finset.card_biUnion
  intro φ hφ ψ hψ hne
  exact disjoint_packedIndependentSupport H S hM (hFM hφ) (hFM hψ) hne

/-- Uniform activation-support bound `2 * |F| * |S|`, with no overlap
correction. -/
theorem card_biUnion_packedIndependentSupports_le {V : Type u} (H : SimpleGraph V)
    [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M) :
    (F.biUnion fun φ => edges H (S.map φ.mapEdgeSet.toEmbedding)).card ≤
      F.card * (2 * S.card) := by
  rw [card_biUnion_packedIndependentSupports H S hM F hFM]
  calc
    (∑ φ ∈ F, (edges H (S.map φ.mapEdgeSet.toEmbedding)).card) ≤
        ∑ _φ ∈ F, 2 * S.card := by
      apply Finset.sum_le_sum
      intro φ hφ
      have h := card_edges_le H (S.map φ.mapEdgeSet.toEmbedding)
      rwa [card_map_mapEdgeSet] at h
    _ = F.card * (2 * S.card) := by simp

/-- Pointwise overlap of activation supports in the packed family is at most
one, not merely bounded by the number of devices. -/
theorem card_filter_mem_packedIndependentSupports_le_one {V : Type u}
    (H : SimpleGraph V) [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M)
    (f : (graph H).edgeSet) :
    (F.filter fun φ => f ∈ edges H (S.map φ.mapEdgeSet.toEmbedding)).card ≤ 1 := by
  classical
  have hsub : (F.filter fun φ => f ∈ edges H (S.map φ.mapEdgeSet.toEmbedding)) ⊆
      (F.filter fun φ => f ∈ template H (S.map φ.mapEdgeSet.toEmbedding)) := by
    intro φ hφ
    simp only [Finset.mem_filter] at hφ ⊢
    exact ⟨hφ.1, (mem_template H).mpr (Or.inr hφ.2)⟩
  exact (Finset.card_le_card hsub).trans
    (card_filter_mem_packedTemplates_le_one H S hM F hFM f)

/-- Exact uniform base-support size on a finite part of the actual packing. -/
theorem card_independentBaseSupport_packed {V : Type u} (H : SimpleGraph V)
    [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M) :
    (independentBaseSupport H
      (fun φ : {φ // φ ∈ F} => S.map φ.1.mapEdgeSet.toEmbedding)).card =
        F.card * S.card := by
  classical
  rw [card_independentBaseSupport_uniform H _
    (disjoint_packedIndependentAnnuli_fintype H S hM F hFM) S.card
    (fun φ => card_map_mapEdgeSet H φ.1 S)]
  simp

end FK.AGImplant.Sleeve
