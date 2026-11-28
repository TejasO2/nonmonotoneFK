import BBRAG.Timar

/-!
# The closed shell of a finite open cluster

If the open cluster of the origin is finite, the sites outside it that are adjacent to it and
joined to infinity outside it form a finite set of closed sites, connected at distance at most
two, that meets the positive `e₁`-axis at some `(k+1) e₁` with `k` smaller than its size.

Let `C` be the open cluster of the origin, `C ⊆ B_N(0)`, and let `Y` be the component of
`(N+1) e₁` in the complement of `C`; it contains every site outside `B_N(0)` (`d ≥ 2`). The
complement of `Y` is connected (it consists of `C` and of the components of the complement of `C`
other than `Y`, each of them adjacent to `C`), so by `conn2_boundary` the sites of `Y` adjacent
to the complement of `Y` form an `Adj2`-connected set `S`. Every site of `S` is adjacent to `C`,
so it is closed. If `k e₁` is the last site of `C` on the positive `e₁`-axis, the ray beyond it
ends in `Y`, so `(k+1) e₁ ∈ S`; and for every `j ≤ k` the last site of `C` on an `e₂`-ray from a
site of `C` with first coordinate `j` is followed by a site of `S` with first coordinate `j`.
-/

namespace BBR

variable {d : ℕ}

/-! ### Components -/

/-- A site joined to `a` inside `A` is joined to `a` inside the component of `a` in `A`. -/
private theorem containsPath_comp {A : Set (Site d)} {a x : Site d} (h : ContainsPath A a x) :
    ContainsPath {z | ContainsPath A a z} a x := by
  obtain ⟨P, hP, ha, hx, hA⟩ := h
  refine ⟨P, hP, ha, hx, fun z hz => ?_⟩
  exact (hP.1.siteConnected a (List.mem_of_mem_head? ha) z hz).mono fun w hw => hA w hw

/-- The component of `a` in `A` is connected. -/
private theorem comp_connected (A : Set (Site d)) (a : Site d) :
    SiteConnected {z | ContainsPath A a z} := fun _ hx _ hy =>
  (containsPath_comp hx).symm.trans (containsPath_comp hy)

/-- A walk from a site of `B` to a site outside `B` leaves `B` through a step `u ~ v`, where `u`
is joined to the start inside `B`. -/
private theorem walk_exit {B : Set (Site d)} {P : List (Site d)} (hP : IsWalk P) {x y : Site d}
    (hx : P.head? = some x) (hy : P.getLast? = some y) (hxB : x ∈ B) (hyB : y ∉ B) :
    ∃ u v, Adj u v ∧ v ∉ B ∧ ContainsPath B x u := by
  induction P generalizing x with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hy
      subst hy
      exact absurd hxB hyB
    | cons b l =>
      have hab : Adj a b := hP.2.rel
      have hW : IsWalk (b :: l) := ⟨List.cons_ne_nil b l, hP.2.of_cons⟩
      rw [List.getLast?_cons_cons] at hy
      by_cases hbB : b ∈ B
      · obtain ⟨u, v, huv, hvB, hbu⟩ := ih hW rfl hy hbB
        exact ⟨u, v, huv, hvB, (containsPath_of_adj hxB hbB hab).trans hbu⟩
      · exact ⟨a, b, hab, hbB, containsPath_refl hxB⟩

/-- Discrete intermediate values of a coordinate along a walk. -/
private theorem walk_coord {P : List (Site d)} (hP : IsWalk P) {x y : Site d}
    (hx : P.head? = some x) (hy : P.getLast? = some y) (i : Fin d) {s : ℤ}
    (hs : x i ≤ s ∧ s ≤ y i) : ∃ z ∈ P, z i = s := by
  induction P generalizing x with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    by_cases has : a i = s
    · exact ⟨a, List.mem_cons_self, has⟩
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hy
      subst hy
      exact absurd (le_antisymm hs.1 hs.2) has
    | cons b l =>
      have hab : Adj a b := hP.2.rel
      have hW : IsWalk (b :: l) := ⟨List.cons_ne_nil b l, hP.2.of_cons⟩
      rw [List.getLast?_cons_cons] at hy
      have h1 := abs_sub_apply_le_dist1 a b i
      rw [show dist1 a b = 1 from hab, abs_le] at h1
      obtain ⟨z, hz, hzs⟩ := ih hW rfl hy (by omega)
      exact ⟨z, List.mem_cons_of_mem a hz, hzs⟩

/-- A bounded predicate on `ℕ` that holds at `0` has a last witness. -/
private theorem exists_last (P : ℕ → Prop) (h0 : P 0) (B : ℕ) (hB : ∀ t, P t → t ≤ B) :
    ∃ t, P t ∧ ∀ s, t < s → ¬ P s := by
  by_contra h
  push Not at h
  have key : ∀ n, ∃ t, n ≤ t ∧ P t := by
    intro n
    induction n with
    | zero => exact ⟨0, le_rfl, h0⟩
    | succ n ih =>
      obtain ⟨t, hnt, ht⟩ := ih
      obtain ⟨s, hts, hs⟩ := h t ht
      exact ⟨s, by omega, hs⟩
  obtain ⟨t, ht, hPt⟩ := key (B + 1)
  have := hB t hPt
  omega

/-! ### Rays and the outside of a ball -/

/-- `t ≤ |c + t u| + |c|` for a unit vector `u` and `t ≥ 0`. -/
private theorem le_norm1_add_smul (c u : Site d) (hu : IsUnitVec u) (t : ℤ) (ht : 0 ≤ t) :
    t ≤ norm1 (c + t • u) + norm1 c := by
  have h := norm1_add_le (c + t • u) (-c)
  rw [show c + t • u + -c = t • u by abel, norm1_smul, norm1_neg, show norm1 u = 1 from hu,
    abs_of_nonneg ht, mul_one] at h
  exact h

/-- The segment `c + u, c + 2u, …, c + (t+1) u` along a unit vector `u`. -/
private theorem containsPath_segment {A : Set (Site d)} (c u : Site d) (hu : IsUnitVec u) :
    ∀ t : ℕ, (∀ s : ℕ, 1 ≤ s → s ≤ t + 1 → c + (s : ℤ) • u ∈ A) →
      ContainsPath A (c + u) (c + ((t : ℤ) + 1) • u)
  | 0, h => by
    have h1 := h 1 le_rfl le_rfl
    simp only [Nat.cast_one, one_smul] at h1
    simpa using containsPath_refl h1
  | t + 1, h => by
    have ih := containsPath_segment c u hu t fun s hs1 hs2 => h s hs1 (by omega)
    have h1 := h (t + 1) (by omega) (by omega)
    have h2 := h (t + 2) (by omega) le_rfl
    have e1' : c + (((t + 1 : ℕ) : ℤ) + 1) • u = (c + ((t : ℤ) + 1) • u) + u := by
      push_cast
      rw [add_smul _ _ u, one_smul, add_assoc]
    have e2' : ((t + 2 : ℕ) : ℤ) = ((t + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [e2'] at h2
    push_cast at h1
    refine ih.trans (containsPath_of_adj h1 h2 ?_)
    rw [adj_iff_exists_unitVec]
    exact ⟨u, hu, e1'⟩

/-- Every site outside `B_N(0)` is joined to `(N+1) e₁` outside `B_N(0)` (`d ≥ 2`). -/
private theorem outside_connected (hd : 2 ≤ d) (N : ℕ) :
    ∀ m : ℕ, ∀ x : Site d, norm1 x = (N : ℤ) + 1 + m →
      ContainsPath {z | (N : ℤ) < norm1 z} x (((N : ℤ) + 1) • e1) := by
  have hn : ∀ n : ℤ, 0 ≤ n → norm1 (n • (e1 : Site d)) = n := fun n hn => by
    rw [norm1_smul_e1 (by omega), abs_of_nonneg hn]
  intro m
  induction m with
  | zero =>
    intro x hx
    have hc := two_layers_connected hd ((N : ℤ) + 1) (by omega)
    have h1 := hc x (Or.inl (by simpa using hx)) (((N : ℤ) + 1) • e1)
      (Or.inl (hn _ (by omega)))
    refine h1.mono fun z hz => ?_
    simp only [Set.mem_ofPred_eq] at hz ⊢
    omega
  | succ m ih =>
    intro x hx
    have hc := two_layers_connected hd ((N : ℤ) + 1 + m) (by omega)
    have h1 := hc x (Or.inr (by push_cast at hx; linarith)) (((N : ℤ) + 1 + m) • e1)
      (Or.inl (hn _ (by omega)))
    refine (h1.mono fun z hz => ?_).trans (ih _ (hn _ (by omega)))
    simp only [Set.mem_ofPred_eq] at hz ⊢
    omega

/-! ### The shell -/

theorem finite_cluster_shell (hd : 2 ≤ d) (ω : Set (Site d)) (h0 : (0 : Site d) ∈ ω)
    (hfin : {x | ContainsPath ω 0 x}.Finite) :
    ∃ S : Finset (Site d), (∀ x ∈ S, x ∉ ω) ∧ Conn2 (↑S : Set (Site d)) ∧
      ∃ k : ℕ, k < S.card ∧ ((k : ℤ) + 1) • (e1 : Site d) ∈ S := by
  classical
  -- the open cluster `C` of the origin, inside `B_N(0)`
  set C : Set (Site d) := {x | ContainsPath ω 0 x}
  have h0C : (0 : Site d) ∈ C := containsPath_refl h0
  have hCconn : SiteConnected C := comp_connected ω 0
  have hCcl : ∀ x ∈ C, ∀ y ∈ ω, Adj x y → y ∈ C := fun x hx y hy hxy =>
    ContainsPath.trans hx (containsPath_of_adj (ContainsPath.mem_right hx) hy hxy)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ x ∈ C, norm1 x ≤ N := by
    obtain ⟨M, hM⟩ := (hfin.image norm1).bddAbove
    refine ⟨M.toNat, fun x hx => ?_⟩
    have := hM (Set.mem_image_of_mem norm1 hx)
    omega
  have hCball : ∀ x ∈ C, x ∈ ball (0 : Site d) N := fun x hx => by
    rw [mem_ball, dist1_zero_right]
    exact hN x hx
  -- the component `Y` of `(N+1) e₁` in the complement of `C`
  set p : Site d := ((N : ℤ) + 1) • e1
  set Y : Set (Site d) := {x | ContainsPath Cᶜ p x}
  have hYC : ∀ x ∈ Y, x ∉ C := fun x hx => ContainsPath.mem_right hx
  have hYcl : ∀ x ∈ Y, ∀ y, y ∉ C → Adj x y → y ∈ Y := fun x hx y hy hxy =>
    ContainsPath.trans hx (containsPath_of_adj (ContainsPath.mem_right hx) hy hxy)
  -- sites outside `B_N(0)` lie in `Y`
  have hfar : ∀ x : Site d, (N : ℤ) < norm1 x → x ∈ Y := by
    intro x hx
    have h := outside_connected hd N (norm1 x - N - 1).toNat x (by omega)
    refine (ContainsPath.mono (A := {z | (N : ℤ) < norm1 z}) (B := Cᶜ) ?_ h).symm
    intro z hz hzC
    have := hN z hzC
    simp only [Set.mem_ofPred_eq] at hz
    omega
  -- a ray leaving `C` for good ends in `Y`
  have hray : ∀ c u : Site d, IsUnitVec u → (∀ s : ℕ, 1 ≤ s → c + (s : ℤ) • u ∉ C) →
      c + u ∈ Y := by
    intro c u hu hc
    have h1 := containsPath_segment (A := Cᶜ) c u hu (N + (norm1 c).toNat)
      fun s hs1 _ => hc s hs1
    have h2 : (N : ℤ) < norm1 (c + (((N + (norm1 c).toNat : ℕ) : ℤ) + 1) • u) := by
      have := le_norm1_add_smul c u hu (((N + (norm1 c).toNat : ℕ) : ℤ) + 1) (by positivity)
      push_cast at this ⊢
      omega
    exact ContainsPath.trans (hfar _ h2) h1.symm
  -- the complement of `Y` is connected
  have hYc : SiteConnected Yᶜ := by
    have hCY : ∀ x ∈ C, ContainsPath Yᶜ x 0 := fun x hx =>
      (hCconn x hx 0 h0C).mono fun z hz hzY => hYC z hzY hz
    have key : ∀ x ∈ Yᶜ, ContainsPath Yᶜ x 0 := by
      intro x hx
      by_cases hxC : x ∈ C
      · exact hCY x hxC
      · obtain ⟨P, hP, hPx, hP0, -⟩ := exists_monotone_path x 0
        obtain ⟨u, v, huv, hvC, hxu⟩ :=
          walk_exit (B := Cᶜ) hP.1 hPx hP0 hxC (fun h => h h0C)
        have hvC' : v ∈ C := by
          by_contra h
          exact hvC h
        have h1 : ContainsPath Yᶜ x u := by
          refine (containsPath_comp hxu).mono fun z hz hzY => hx ?_
          exact ContainsPath.trans hzY (ContainsPath.symm hz)
        have h2 : ContainsPath Yᶜ u v :=
          containsPath_of_adj h1.mem_right (fun h => hYC v h hvC') huv
        exact h1.trans (h2.trans (hCY v hvC'))
    exact fun x hx y hy => (key x hx).trans (key y hy).symm
  -- the boundary `S` of `Y`
  have hS := conn2_boundary Y Yᶜ (comp_connected Cᶜ p) disjoint_compl_right hYc
    (fun _ _ z hz _ => hz)
  set S : Set (Site d) := {x | x ∈ Y ∧ ∃ y ∈ Yᶜ, Adj x y}
  have hSC : ∀ x ∈ S, x ∉ C ∧ ∃ y ∈ C, Adj x y := by
    rintro x ⟨hxY, y, hyY, hxy⟩
    refine ⟨hYC x hxY, y, ?_, hxy⟩
    by_contra hyC
    exact hyY (hYcl x hxY y hyC hxy)
  have hSfin : S.Finite := by
    refine (ball_finite (0 : Site d) ((N : ℤ) + 1)).subset fun x hx => ?_
    obtain ⟨-, y, hyC, hxy⟩ := hSC x hx
    exact adj_mem_ball_succ (hCball y hyC) (adj_comm.mp hxy)
  -- a site `c ∈ C` followed by a ray outside `C` gives the site `c + u` of `S`
  have hmemS : ∀ c u : Site d, IsUnitVec u → c ∈ C → (∀ s : ℕ, 1 ≤ s → c + (s : ℤ) • u ∉ C) →
      c + u ∈ hSfin.toFinset := by
    intro c u hu hc hcu
    rw [Set.Finite.mem_toFinset]
    refine ⟨hray c u hu hcu, c, fun h => hYC c h hc, ?_⟩
    rw [adj_iff_exists_unitVec]
    exact ⟨-u, hu.neg, by abel⟩
  refine ⟨hSfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx hxω
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨hxC, y, hyC, hxy⟩ := hSC x hx
    exact hxC (hCcl y hyC x hxω (adj_comm.mp hxy))
  · rw [Set.Finite.coe_toFinset]
    exact hS
  -- the last site `k e₁` of `C` on the positive `e₁`-axis
  have hd1 : 1 ≤ d := by omega
  have he1 : IsUnitVec (e1 : Site d) := by
    have h := norm1_smul_e1 (d := d) hd1 1
    rw [one_smul] at h
    exact h
  obtain ⟨k, hk, hkmax⟩ := exists_last (fun j : ℕ => ((j : ℤ) • (e1 : Site d)) ∈ C)
    (by simpa using h0C) N (fun j hj => by
      have h := hN _ hj
      rw [norm1_smul_e1 hd1, abs_of_nonneg (by positivity)] at h
      exact_mod_cast h)
  refine ⟨k, ?_, ?_⟩
  · -- for every `j ≤ k`, a site of `S` with first coordinate `j`
    obtain ⟨i0, hi0⟩ : ∃ i : Fin d, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
    obtain ⟨i1, hi1⟩ : ∃ i : Fin d, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
    have hne : i0 ≠ i1 := fun h => by
      rw [h] at hi0
      omega
    have hu1 : IsUnitVec (Pi.single i1 (1 : ℤ) : Site d) := isUnitVec_single i1 (Or.inl rfl)
    have hcol : ∀ j : ℕ, j ≤ k → ∃ x ∈ hSfin.toFinset, x i0 = j := by
      intro j hj
      obtain ⟨P, hP, hP0, hPk, hPC⟩ := hCconn 0 h0C _ hk
      obtain ⟨c, hcP, hcj⟩ := walk_coord hP.1 hP0 hPk i0 (s := (j : ℤ))
        ⟨by simp, by simp [e1, hi0]; exact_mod_cast hj⟩
      have hcC := hPC c hcP
      obtain ⟨t, ht, htmax⟩ := exists_last
        (fun t : ℕ => c + (t : ℤ) • (Pi.single i1 (1 : ℤ) : Site d) ∈ C)
        (by simpa using hcC) (N + (norm1 c).toNat) (fun t ht => by
          have h1 := hN _ ht
          have h2 := le_norm1_add_smul c _ hu1 (t : ℤ) (by positivity)
          omega)
      refine ⟨c + (t : ℤ) • Pi.single i1 1 + Pi.single i1 1, hmemS _ _ hu1 ht ?_, ?_⟩
      · intro s hs hmem
        apply htmax (t + s) (by omega)
        rw [Nat.cast_add, add_smul, ← add_assoc]
        exact hmem
      · simp [Pi.single_eq_of_ne hne, hcj]
    have hsub : Finset.range (k + 1) ⊆ hSfin.toFinset.image (fun x => (x i0).toNat) := by
      intro j hj
      rw [Finset.mem_range] at hj
      obtain ⟨x, hx, hxj⟩ := hcol j (by omega)
      exact Finset.mem_image.mpr ⟨x, hx, by rw [hxj]; simp⟩
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_range] at this
    omega
  · -- the site `(k+1) e₁` of `S`
    have h := hmemS _ e1 he1 hk fun s hs hmem => by
      apply hkmax (k + s) (by omega)
      rw [Nat.cast_add, add_smul]
      exact hmem
    rwa [add_smul, one_smul]

end BBR
