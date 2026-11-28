import BBRAG.Parity

/-!
# Boundary connectivity (Timár's argument for `ℤ^d`)

Let `X` be connected and `Y` a connected set of sites outside `X` that is closed under adjacency
outside `X` (a component of the complement of `X`). Then the sites of `X` adjacent to `Y` are
connected for adjacency at distance at most two.

Proof by parity. If the boundary `∂ = {x ∈ X | x is adjacent to Y}` were not connected for
`Adj2`, let `P` be the `Adj2`-component of a site `p ∈ ∂` inside `∂`, and `q ∈ ∂ \ P`. Count the
edges between `Y` and `P`. A unit square has an even number of them: its four sites are pairwise at
distance at most two, so if one of them lies in `P`, every site of the square in `∂` lies in `P`,
and then (by the closure of `Y`) its edges between `Y` and `P` are exactly its edges between `Y`
and the complement of `Y`. On the other hand the closed walk `p`, (a path in `Y` from a neighbour of
`p` to a neighbour of `q`), (a path in `X` from `q` back to `p`) has exactly one such edge. This
contradicts `even_edgeCount_closed`.
-/

namespace BBR

variable {d : ℕ}

theorem conn2_boundary (X Y : Set (Site d)) (hX : SiteConnected X) (hXY : Disjoint X Y)
    (hY : SiteConnected Y) (hcl : ∀ y ∈ Y, ∀ z, z ∉ X → Adj y z → z ∈ Y) :
    Conn2 {x | x ∈ X ∧ ∃ y ∈ Y, Adj x y} := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Site d), S = {x | x ∈ X ∧ ∃ y ∈ Y, Adj x y} := ⟨_, rfl⟩
  have hSmem : ∀ x, x ∈ S ↔ x ∈ X ∧ ∃ y ∈ Y, Adj x y := by
    intro x
    rw [hSdef]
    rfl
  rw [← hSdef]
  intro p hp q hq
  by_contra hne
  -- `P`: the sites of `S` joined to `p` by an `Adj2`-walk in `S`
  obtain ⟨P, hPdef⟩ : ∃ P : Set (Site d), ∀ z, z ∈ P ↔ ∃ L : List (Site d), L.head? = some p ∧
      L.getLast? = some z ∧ L.IsChain Adj2 ∧ ∀ w ∈ L, w ∈ S := ⟨_, fun _ => Iff.rfl⟩
  have hpP : p ∈ P := (hPdef p).mpr ⟨[p], rfl, rfl, List.isChain_singleton p, by simpa using hp⟩
  have hqP : q ∉ P := fun h => hne ((hPdef q).mp h)
  have hPS : ∀ z ∈ P, z ∈ S := by
    intro z hz
    obtain ⟨L, -, hl, -, hm⟩ := (hPdef z).mp hz
    exact hm z (List.mem_of_mem_getLast? hl)
  have hPX : ∀ z ∈ P, z ∈ X := fun z hz => ((hSmem z).mp (hPS z hz)).1
  have hPY : ∀ z ∈ P, z ∉ Y := fun z hz => Set.disjoint_left.mp hXY (hPX z hz)
  have hstep : ∀ u ∈ P, ∀ w ∈ S, Adj2 u w → w ∈ P := by
    intro u hu w hw huw
    obtain ⟨L, hh, hl, hc, hm⟩ := (hPdef u).mp hu
    refine (hPdef w).mpr ⟨L ++ [w], ?_, List.getLast?_concat, ?_, ?_⟩
    · rw [List.head?_append, hh]
      rfl
    · refine hc.append (List.isChain_singleton w) ?_
      intro x hx z hz
      rw [hl, Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hx hz
      exact huw
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      · exact hm z h
      · rw [List.mem_singleton.mp h]
        exact hw
  have hclose : ∀ u ∈ P, ∀ w ∈ S, dist1 u w ≤ 2 → w ∈ P := by
    intro u hu w hw h2
    by_cases huw : u = w
    · rw [← huw]
      exact hu
    · refine hstep u hu w hw ⟨?_, h2⟩
      have h0 := dist1_nonneg u w
      have h1 : dist1 u w ≠ 0 := fun h => huw ((dist1_eq_zero_iff u w).mp h)
      omega
  -- the edges between `Y` and `P`
  obtain ⟨e, he⟩ : ∃ e : Site d → Site d → Prop,
      ∀ u v, e u v ↔ (u ∈ Y ∧ v ∈ P) ∨ (v ∈ Y ∧ u ∈ P) := ⟨_, fun _ _ => Iff.rfl⟩
  have hsym : ∀ x y, e x y ↔ e y x := fun x y => by
    rw [he, he]
    exact Or.comm
  -- a walk none of whose steps is an `e`-step has `e`-count zero
  have hzero : ∀ L : List (Site d), L.IsChain (fun u v => ¬ e u v) → edgeCount e L = 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons a t ih =>
      cases t with
      | nil => rfl
      | cons b t =>
        rw [List.isChain_cons_cons] at hL
        simp [edgeCount, hL.1, ih hL.2]
  -- if each end of the edge `vw` lies in `P` once it lies in `S`, then `vw` is an `e`-edge iff
  -- exactly one of its ends is in `Y`
  have hkey : ∀ v w, Adj v w → (v ∈ S → v ∈ P) → (w ∈ S → w ∈ P) →
      (e v w ↔ (v ∈ Y ∧ w ∉ Y) ∨ (w ∈ Y ∧ v ∉ Y)) := by
    intro v w hvw hv hw
    rw [he]
    constructor
    · rintro (⟨hvY, hwP⟩ | ⟨hwY, hvP⟩)
      · exact Or.inl ⟨hvY, hPY w hwP⟩
      · exact Or.inr ⟨hwY, hPY v hvP⟩
    · rintro (⟨hvY, hwY⟩ | ⟨hwY, hvY⟩)
      · have hwX : w ∈ X := by
          by_contra hwX
          exact hwY (hcl v hvY w hwX hvw)
        exact Or.inl ⟨hvY, hw ((hSmem w).mpr ⟨hwX, v, hvY, adj_comm.mp hvw⟩)⟩
      · have hvX : v ∈ X := by
          by_contra hvX
          exact hvY (hcl w hwY v hvX (adj_comm.mp hvw))
        exact Or.inr ⟨hwY, hv ((hSmem v).mpr ⟨hvX, w, hwY, hvw⟩)⟩
  -- every unit square has an even number of `e`-edges
  have hsq : ∀ x a b : Site d, IsUnitVec a → IsUnitVec b → Orth a b →
      Even (edgeCount e [x, x + a, x + a + b, x + b, x]) := by
    intro x a b ha hb _
    have h01 : Adj x (x + a) := (adj_iff_exists_unitVec _ _).mpr ⟨a, ha, rfl⟩
    have h12 : Adj (x + a) (x + a + b) := (adj_iff_exists_unitVec _ _).mpr ⟨b, hb, rfl⟩
    have h32 : Adj (x + b) (x + a + b) := (adj_iff_exists_unitVec _ _).mpr ⟨a, ha, by abel⟩
    have h03 : Adj x (x + b) := (adj_iff_exists_unitVec _ _).mpr ⟨b, hb, rfl⟩
    have e01 : dist1 x (x + a) = 1 := h01
    have e12 : dist1 (x + a) (x + a + b) = 1 := h12
    have e32 : dist1 (x + b) (x + a + b) = 1 := h32
    have e03 : dist1 x (x + b) = 1 := h03
    have d02 : dist1 x (x + a + b) ≤ 2 := by
      linarith [dist1_triangle x (x + a) (x + a + b)]
    have d13 : dist1 (x + a) (x + b) ≤ 2 := by
      linarith [dist1_triangle (x + a) x (x + b), dist1_comm (x + a) x]
    have hV : ∀ u ∈ [x, x + a, x + a + b, x + b], ∀ w ∈ [x, x + a, x + a + b, x + b],
        dist1 u w ≤ 2 := by
      intro u hu w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hw
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
        first | (rw [dist1_self]; norm_num) | linarith | (rw [dist1_comm]; linarith)
    by_cases hA : x ∈ P ∨ x + a ∈ P ∨ x + a + b ∈ P ∨ x + b ∈ P
    · have hall : ∀ w ∈ [x, x + a, x + a + b, x + b], w ∈ S → w ∈ P := by
        intro w hw hwS
        rcases hA with h | h | h | h
        · exact hclose _ h w hwS (hV _ (by simp) w hw)
        · exact hclose _ h w hwS (hV _ (by simp) w hw)
        · exact hclose _ h w hwS (hV _ (by simp) w hw)
        · exact hclose _ h w hwS (hV _ (by simp) w hw)
      have k01 := hkey x (x + a) h01 (hall _ (by simp)) (hall _ (by simp))
      have k12 := hkey (x + a) (x + a + b) h12 (hall _ (by simp)) (hall _ (by simp))
      have k23 := hkey (x + a + b) (x + b) (adj_comm.mp h32) (hall _ (by simp)) (hall _ (by simp))
      have k30 := hkey (x + b) x (adj_comm.mp h03) (hall _ (by simp)) (hall _ (by simp))
      simp only [edgeCount]
      by_cases y0 : x ∈ Y <;> by_cases y1 : x + a ∈ Y <;> by_cases y2 : x + a + b ∈ Y <;>
        by_cases y3 : x + b ∈ Y <;> simp [k01, k12, k23, k30, y0, y1, y2, y3, Nat.even_iff]
    · simp only [not_or] at hA
      obtain ⟨n0, n1, n2, n3⟩ := hA
      have hn : ∀ u v, u ∉ P → v ∉ P → ¬ e u v := by
        intro u v hu hv h
        rw [he] at h
        rcases h with ⟨_, h⟩ | ⟨_, h⟩
        · exact hv h
        · exact hu h
      simp only [edgeCount]
      simp [hn _ _ n0 n1, hn _ _ n1 n2, hn _ _ n2 n3, hn _ _ n3 n0]
  -- a closed walk with exactly one `e`-edge
  obtain ⟨hpX, y, hyY, hpy⟩ := (hSmem p).mp hp
  obtain ⟨hqX, y', hy'Y, hqy'⟩ := (hSmem q).mp hq
  obtain ⟨Ly, hLy, hLyh, hLyl, hLyY⟩ := hY y hyY y' hy'Y
  obtain ⟨Lx, hLx, hLxh, hLxl, hLxX⟩ := hX q hqX p hpX
  obtain ⟨ly, rfl⟩ := List.head?_eq_some_iff.mp hLyh
  have hjoin : ∀ u ∈ (y :: ly).getLast?, ∀ v ∈ Lx.head?, u = y' ∧ v = q := by
    intro u hu v hv
    rw [hLyl, Option.mem_def, Option.some.injEq] at hu
    rw [hLxh, Option.mem_def, Option.some.injEq] at hv
    exact ⟨hu.symm, hv.symm⟩
  have hW : IsWalk (p :: (y :: ly ++ Lx)) := by
    refine ⟨List.cons_ne_nil _ _, List.IsChain.cons_cons hpy ?_⟩
    refine hLy.1.2.append hLx.1.2 ?_
    intro u hu v hv
    obtain ⟨rfl, rfl⟩ := hjoin u hu v hv
    exact adj_comm.mp hqy'
  have hWcl : (p :: (y :: ly ++ Lx)).head? = (p :: (y :: ly ++ Lx)).getLast? := by
    rw [List.getLast?_cons, List.getLast?_append_of_ne_nil _ hLx.1.1, hLxl]
    rfl
  have hcount : edgeCount e (p :: (y :: ly ++ Lx)) = 1 := by
    have hepy : e p y := (he p y).mpr (Or.inr ⟨hyY, hpP⟩)
    have c1 : (y :: ly).IsChain (fun u v => ¬ e u v) := by
      refine hLy.1.2.imp_of_mem_imp ?_
      intro u v hu hv _ h
      rw [he] at h
      rcases h with ⟨_, hvP⟩ | ⟨_, huP⟩
      · exact hPY v hvP (hLyY v hv)
      · exact hPY u huP (hLyY u hu)
    have c2 : Lx.IsChain (fun u v => ¬ e u v) := by
      refine hLx.1.2.imp_of_mem_imp ?_
      intro u v hu hv _ h
      rw [he] at h
      rcases h with ⟨huY, _⟩ | ⟨hvY, _⟩
      · exact Set.disjoint_left.mp hXY (hLxX u hu) huY
      · exact Set.disjoint_left.mp hXY (hLxX v hv) hvY
    have c3 : (y :: ly ++ Lx).IsChain (fun u v => ¬ e u v) := by
      refine c1.append c2 ?_
      intro u hu v hv h
      obtain ⟨rfl, rfl⟩ := hjoin u hu v hv
      rw [he] at h
      rcases h with ⟨_, hqP'⟩ | ⟨hqY, _⟩
      · exact hqP hqP'
      · exact Set.disjoint_left.mp hXY hqX hqY
    have h0 := hzero _ c3
    show edgeCount e (p :: y :: (ly ++ Lx)) = 1
    rw [edgeCount]
    simp only [List.cons_append] at h0
    simp [hepy, h0]
  have hEven := even_edgeCount_closed e hsym hsq _ hW hWcl
  rw [hcount] at hEven
  exact Nat.not_even_one hEven

end BBR
