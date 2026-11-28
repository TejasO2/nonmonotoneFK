import BBRAG.Defs

/-!
# Reduction of the crossing event to a finite box

`R_L` depends only on the open sites in `B_{L + 2 r_E}` and the activation sites in
`B_{L + r_E}`; p-pivotal sites lie in `B_{L + 2 r_E}`, so the modification of Claim 4 stays in
`B_{L + 2 r_E + R}`.
-/

namespace BBR

variable {d : ℕ}

/-! ### The box `B_N(0)` -/

private theorem mem_boxFin_iff {N : ℕ} {x : Site d} :
    x ∈ boxFin d N ↔ x ∈ ball (0 : Site d) N := by
  unfold boxFin
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 := abs_apply_le_norm1 x i
  have h2 : norm1 x ≤ N := by rwa [mem_ball, dist1_zero_right] at h
  rw [abs_le] at h1
  constructor <;> linarith

/-! ### Crossing depends only on `B_L(0)` -/

/-- A walk starting in `B_L(0)` and ending outside the open ball `{|x| < L}` meets `S_L`, and the
part of the walk before its first site on `S_L` stays in `B_L(0)`. -/
private theorem walk_reach_sphere {L : ℕ} {A : Set (Site d)} (P : List (Site d)) :
    ∀ x : Site d, P.IsChain Adj → P.head? = some x → dist1 x 0 ≤ L →
      (∀ y ∈ P.getLast?, (L : ℤ) ≤ dist1 y 0) → (∀ z ∈ P, z ∈ A) →
      ∃ z ∈ sphere (0 : Site d) L, ContainsPath (A ∩ ball 0 L) x z := by
  induction P with
  | nil =>
    intro x _ hx
    simp at hx
  | cons a l ih =>
    intro x hc hx hxL hy hA
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    have haA : a ∈ A ∩ ball 0 L := ⟨hA a List.mem_cons_self, hxL⟩
    by_cases haL : dist1 a 0 = L
    · exact ⟨a, haL, containsPath_refl haA⟩
    cases l with
    | nil =>
      have := hy a (by simp)
      omega
    | cons b l =>
      have hab : Adj a b := hc.rel
      have hbL : dist1 b 0 ≤ L := by
        rcases adj_layer hab 0 with h | h <;> omega
      obtain ⟨z, hz, hbz⟩ := ih b hc.of_cons rfl hbL
        (fun y hy' => hy y (by rwa [List.getLast?_cons_cons]))
        (fun z hz => hA z (List.mem_cons_of_mem a hz))
      exact ⟨z, hz, (containsPath_of_adj haA ⟨hA b (by simp), hbL⟩ hab).trans hbz⟩

private theorem crosses_iff_inter_ball (L : ℕ) (A : Set (Site d)) :
    Crosses L A ↔ Crosses L (A ∩ ball 0 L) := by
  constructor
  · rintro ⟨y, hy, hP⟩
    obtain ⟨P, hW, hh, hl, hA⟩ := (containsPath_iff_walk A 0 y).1 hP
    refine walk_reach_sphere P 0 hW.2 hh (by simp) ?_ hA
    intro z hz
    rw [hl, Option.mem_def, Option.some.injEq] at hz
    subst hz
    exact le_of_eq hy.symm
  · rintro ⟨y, hy, hP⟩
    exact ⟨y, hy, hP.mono Set.inter_subset_left⟩

private theorem crosses_congr {L : ℕ} {A B : Set (Site d)}
    (h : ∀ x ∈ ball (0 : Site d) L, x ∈ A ↔ x ∈ B) : Crosses L A ↔ Crosses L B := by
  have hAB : A ∩ ball 0 L = B ∩ ball 0 L := by
    ext x
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(h x h2).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(h x h2).2 h1, h2⟩
  rw [crosses_iff_inter_ball L A, crosses_iff_inter_ball L B, hAB]

/-! ### Locality of the enhanced configuration -/

/-- `E(ω, α) ∩ B_M(0)` depends only on `ω ∩ B_{M + 2 r_E}(0)` and `α ∩ B_{M + r_E}(0)`. -/
private theorem mem_enhanced_of_agree (E0 : Set (Site d) → Set (Site d)) (rE : ℕ)
    (hE : HasRange E0 rE) (M : ℤ) {ω ω₁ α α₁ : Set (Site d)}
    (hω : ∀ x ∈ ball (0 : Site d) (M + 2 * rE), x ∈ ω ↔ x ∈ ω₁)
    (hα : ∀ x ∈ ball (0 : Site d) (M + rE), x ∈ α ↔ x ∈ α₁)
    {x : Site d} (hx : x ∈ ball (0 : Site d) M) (h : x ∈ enhanced E0 ω α) :
    x ∈ enhanced E0 ω₁ α₁ := by
  have hrE : (0 : ℤ) ≤ rE := Int.natCast_nonneg rE
  rw [mem_ball] at hx
  unfold enhanced at h ⊢
  rcases h with h | h
  · left
    exact (hω x (by rw [mem_ball]; omega)).1 h
  · right
    simp only [Set.mem_iUnion] at h ⊢
    obtain ⟨v, hv, hxv⟩ := h
    rw [mem_translate] at hxv
    have h1 : dist1 (x - v) 0 ≤ rE := hE.2 _ hxv
    have h2 : dist1 x v = dist1 (x - v) 0 := by
      rw [dist1_zero_right]
      rfl
    have h3 := dist1_triangle v x 0
    rw [dist1_comm v x] at h3
    have hv0 : v ∈ ball (0 : Site d) (M + rE) := by
      rw [mem_ball]
      omega
    refine ⟨v, (hα v hv0).1 hv, ?_⟩
    rw [mem_translate]
    have key : E0 (translate ω (-v)) = E0 (translate ω₁ (-v)) := by
      apply hE.1
      ext z
      simp only [Set.mem_inter_iff, mem_translate, sub_neg_eq_add, mem_ball]
      have hz : dist1 z 0 ≤ rE → z + v ∈ ball (0 : Site d) (M + 2 * rE) := by
        intro hz
        have h4 := dist1_triangle (z + v) v 0
        have h5 : dist1 (z + v) v = dist1 z 0 := by
          rw [← dist1_add_right z 0 v, zero_add]
        rw [mem_ball]
        rw [mem_ball] at hv0
        omega
      constructor
      · rintro ⟨h6, h7⟩
        exact ⟨(hω _ (hz h7)).1 h6, h7⟩
      · rintro ⟨h6, h7⟩
        exact ⟨(hω _ (hz h7)).2 h6, h7⟩
    rw [← key]
    exact hxv

/-- **Locality of crossing.** `R_L` depends only on the open sites in `B_{L + 2 r_E}(0)` and the
activation sites in `B_{L + r_E}(0)`. -/
private theorem crosses_enhanced_congr (E0 : Set (Site d) → Set (Site d)) (rE : ℕ)
    (hE : HasRange E0 rE) (L : ℕ) {ω ω₁ α α₁ : Set (Site d)}
    (hω : ∀ x ∈ ball (0 : Site d) (L + 2 * rE), x ∈ ω ↔ x ∈ ω₁)
    (hα : ∀ x ∈ ball (0 : Site d) (L + rE), x ∈ α ↔ x ∈ α₁) :
    Crosses L (enhanced E0 ω α) ↔ Crosses L (enhanced E0 ω₁ α₁) :=
  crosses_congr fun _ hx =>
    ⟨mem_enhanced_of_agree E0 rE hE L hω hα hx,
      mem_enhanced_of_agree E0 rE hE L (fun y hy => (hω y hy).symm)
        (fun y hy => (hα y hy).symm) hx⟩

/-! ### The indicator `RLind` -/

private theorem RLind_eq_one_iff (E0 : Set (Site d) → Set (Site d)) (L : ℕ)
    (η ζ : Finset (Site d)) : RLind E0 L η ζ = 1 ↔ Crosses L (enhanced E0 ↑η ↑ζ) := by
  unfold RLind
  split_ifs with h <;> simp [h]

private theorem RLind_eq_zero_iff (E0 : Set (Site d) → Set (Site d)) (L : ℕ)
    (η ζ : Finset (Site d)) : RLind E0 L η ζ = 0 ↔ ¬ Crosses L (enhanced E0 ↑η ↑ζ) := by
  unfold RLind
  split_ifs with h <;> simp [h]

theorem RLind_01 (E0 : Set (Site d) → Set (Site d)) (L : ℕ) (η ζ : Finset (Site d)) :
    RLind E0 L η ζ = 0 ∨ RLind E0 L η ζ = 1 := by
  unfold RLind
  split_ifs <;> simp

/-- `R_L` is increasing in the activation configuration. -/
theorem RLind_mono (E0 : Set (Site d) → Set (Site d)) (L : ℕ) :
    ∀ η ζ ζ' : Finset (Site d), ζ ⊆ ζ' → RLind E0 L η ζ ≤ RLind E0 L η ζ' := by
  intro η ζ ζ' h
  have hsub : enhanced E0 ↑η ↑ζ ⊆ enhanced E0 ↑η ↑ζ' :=
    Set.union_subset_union_right _ (Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 h))
  unfold RLind
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso
    obtain ⟨y, hy, hP⟩ := h1
    exact h2 ⟨y, hy, hP.mono hsub⟩
  · norm_num
  · exact le_rfl

open Classical in
/-- **Locality.** For `N ≥ L + 2 r_E`, the crossing event is determined by the restriction of the
configurations to the box `B_N(0)`. -/
theorem crosses_iff_box (E0 : Set (Site d) → Set (Site d)) (rE : ℕ) (hE : HasRange E0 rE)
    (L N : ℕ) (hN : L + 2 * rE ≤ N) (ω α : Set (Site d)) :
    Crosses L (enhanced E0 ω α) ↔
      RLind E0 L ((boxFin d N).filter (· ∈ ω)) ((boxFin d N).filter (· ∈ α)) = 1 := by
  rw [RLind_eq_one_iff]
  have hrE : (0 : ℤ) ≤ rE := Int.natCast_nonneg rE
  have hN' : (L : ℤ) + 2 * rE ≤ N := by exact_mod_cast hN
  apply crosses_enhanced_congr E0 rE hE L
  · intro x hx
    rw [mem_ball] at hx
    have hxN : x ∈ boxFin d N := mem_boxFin_iff.2 (by rw [mem_ball]; omega)
    simp [hxN]
  · intro x hx
    rw [mem_ball] at hx
    have hxN : x ∈ boxFin d N := mem_boxFin_iff.2 (by rw [mem_ball]; omega)
    simp [hxN]

/-- **Claim 4 in the box.** For `L ≥ L₀` and `N ≥ L + 2 r_E + R`, Claim 4 gives the modification
property of the box `B_N(0)` with `near v = B_N(0) ∩ B_R(v)`. -/
theorem modProp_box (E0 : Set (Site d) → Set (Site d)) (rE : ℕ) (hE : HasRange E0 rE)
    (L₀ R : ℕ) (h4 : Claim4With E0 L₀ R) (L N : ℕ) (hL : L₀ ≤ L) (hN : L + 2 * rE + R ≤ N) :
    ModProp (boxFin d N) (RLind E0 L) (fun v => (boxFin d N).filter (· ∈ ball v R)) := by
  classical
  intro η _ ζ _ v _ h1 h0
  rw [RLind_eq_one_iff, Finset.coe_insert] at h1
  rw [RLind_eq_zero_iff, Finset.coe_erase] at h0
  obtain ⟨ω', α', hagree, w, hw, hs1, hs0⟩ := h4 L hL _ _ v ⟨h1, h0⟩
  have hrE : (0 : ℤ) ≤ rE := Int.natCast_nonneg rE
  have hN' : (L : ℤ) + 2 * rE + R ≤ N := by exact_mod_cast hN
  -- a p-pivotal site lies in `B_{L + 2 r_E}(0)`
  have hv0 : v ∈ ball (0 : Site d) (L + 2 * rE) := by
    by_contra hvn
    apply h0
    refine (crosses_enhanced_congr E0 rE hE L ?_ (fun x _ => Iff.rfl)).1 h1
    intro x hx
    have hxv : x ≠ v := fun h => hvn (h ▸ hx)
    simp [hxv]
  have hwN : w ∈ boxFin d N := by
    rw [mem_boxFin_iff, mem_ball]
    have := dist1_triangle w v 0
    rw [mem_ball] at hw hv0
    omega
  -- the box agrees with `ω'`, `α'` on `B_N(0)`
  have hbox : ∀ x ∈ ball (0 : Site d) (L + 2 * rE), x ∈ boxFin d N := by
    intro x hx
    rw [mem_ball] at hx
    exact mem_boxFin_iff.2 (by rw [mem_ball]; omega)
  have hbox' : ∀ x ∈ ball (0 : Site d) (L + rE), x ∈ boxFin d N := by
    intro x hx
    rw [mem_ball] at hx
    exact mem_boxFin_iff.2 (by rw [mem_ball]; omega)
  refine ⟨(boxFin d N).filter (· ∈ ω'), Finset.mem_powerset.2 (Finset.filter_subset _ _),
    (boxFin d N).filter (· ∈ α'), Finset.mem_powerset.2 (Finset.filter_subset _ _), w,
    Finset.mem_filter.2 ⟨hwN, hw⟩, ?_, ?_, ?_⟩
  · intro x hx hxn
    have hxR : x ∉ ball v R := fun h => hxn (Finset.mem_filter.2 ⟨hx, h⟩)
    obtain ⟨h2, h3⟩ := hagree x hxR
    simp only [Finset.mem_filter, hx, true_and]
    exact ⟨h2, h3⟩
  · rw [RLind_eq_one_iff, Finset.coe_insert]
    refine (crosses_enhanced_congr E0 rE hE L ?_ ?_).1 hs1
    · intro x hx
      simp [hbox x hx]
    · intro x hx
      simp [hbox' x hx]
  · rw [RLind_eq_zero_iff, Finset.coe_erase]
    intro hc
    apply hs0
    refine (crosses_enhanced_congr E0 rE hE L ?_ ?_).1 hc
    · intro x hx
      simp [hbox x hx]
    · intro x hx
      simp [hbox' x hx]

theorem near_card_le (N R : ℕ) (v : Site d) :
    ((boxFin d N).filter (· ∈ ball v R)).card ≤ (boxFin d R).card := by
  refine Finset.card_le_card_of_injOn (fun x => x - v) ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, mem_ball] at hx
    rw [Finset.mem_coe, mem_boxFin_iff, mem_ball, dist1_zero_right]
    exact hx.2
  · intro x _ y _ h
    exact sub_left_injective h

theorem near_symm (N R : ℕ) (v w : Site d) (h : w ∈ (boxFin d N).filter (· ∈ ball v R))
    (hv : v ∈ boxFin d N) : v ∈ (boxFin d N).filter (· ∈ ball w R) := by
  rw [Finset.mem_filter] at h ⊢
  refine ⟨hv, ?_⟩
  rw [mem_ball, dist1_comm]
  exact h.2

end BBR
