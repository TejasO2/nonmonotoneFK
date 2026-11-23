import FK.AGPackingDensity
import FK.EssentialEnhancement

/-!
# A concrete positive-density bounded-range essential-device family

This file instantiates the abstract density and activation-tail results of
`AGPackingDensity` on a genuine graph, to show that they are not vacuous and that
the constants are honest.

The graph is the integer line `ℤ` with bonds `{n, n+1}`.  It is connected,
locally finite and of degree two, and **every** bond lies on a double ray (the
translate of the unit-step double ray), so by
`FK.EssentialEnhancement.essential_of_onDoubleRay` every bond is an
Aizenman--Grimmett essential device.  The selected device family is the
three-periodic subfamily `bond (3k)`; its range is zero (each device is a single
bond), so it is bounded-range, and its devices are pairwise disjoint as
templates.  The distinguished pivots are all multiples of three, which are
within distance one of every integer: the `K`-covering hypothesis with `K = 1`.

The concrete consequences are:

* `density_lower`: three-periodic pivots cannot be replaced by finitely many
  pivots, quantitatively `n + 1 ≤ 3 * |J|` for every finite pivot set `J` and
  every `n`; the density constant is `1/3` with a radius-one ball of `3` edges.
* `activation_tail_le`: the probability that every device in the radius-`n`
  window is inactive is at most `(1 - s)^{2n+1}` for activation rate `s`.
* `activation_tail_eventually`: that bound, hence the all-inactive probability,
  is arbitrarily small.

No critical parameter, no `hAG` and no strict-shift claim is made here.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped Sym2 BigOperators ENNReal

namespace FK.AGPackingDensity.Example

/-! ## The integer line and its bonds -/

/-- The integer line, as a symmetric loopless graph. -/
def line : SimpleGraph ℤ where
  Adj a b := b = a + 1 ∨ a = b + 1
  symm := ⟨by
    intro a b h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h⟩
  loopless := ⟨fun a h => by rcases h with h | h <;> omega⟩

lemma line_adj (a b : ℤ) : line.Adj a b ↔ (b = a + 1 ∨ a = b + 1) := Iff.rfl

/-- The bond `{n, n+1}` of the integer line. -/
def bond (n : ℤ) : line.edgeSet :=
  ⟨s(n, n + 1), by
    rw [SimpleGraph.mem_edgeSet]
    exact Or.inl rfl⟩

lemma bond_injective : Function.Injective bond := by
  intro m n h
  have hv : (s(m, m + 1) : Sym2 ℤ) = s(n, n + 1) := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The double ray through the bond `bond k`, namely the unit-step ray issued
from `k`. -/
def rayFrom (k : ℤ) : FK.EssentialEnhancement.DoubleRay line where
  vertex n := k + n
  vertex_injective := by
    intro m n h
    simp only at h
    omega
  adj n := by
    exact Or.inl (by ring)

/-- Every bond lies on a double ray. -/
theorem bond_onDoubleRay (k : ℤ) : FK.EssentialEnhancement.OnDoubleRay (bond k) := by
  refine ⟨rayFrom k, 0, ?_⟩
  apply Subtype.ext
  simp [FK.EssentialEnhancement.DoubleRay.edge, rayFrom, bond]

/-- **Every bond of the integer line is an essential device.** -/
theorem bond_essential (k : ℤ) :
    FK.EssentialEnhancement.Essential (G := line) (bond k) :=
  FK.EssentialEnhancement.essential_of_onDoubleRay (bond_onDoubleRay k)

/-! ## The edge metric and the three-periodic pivots -/

/-- The integer line metric with explicit finite balls. -/
def zMetric : EdgeMetric ℤ where
  dist a b := (a - b).natAbs
  ball f n := Finset.Icc (f - (n : ℤ)) (f + (n : ℤ))
  mem_ball := by
    intro f n g
    rw [Finset.mem_Icc]
    constructor <;> intro h <;> omega
  dist_comm := by
    intro a b
    omega
  dist_triangle := by
    intro a b c
    have h := Int.natAbs_add_le (a - b) (b - c)
    have he : (a - b) + (b - c) = a - c := by ring
    rwa [he] at h

lemma zMetric_dist (a b : ℤ) : zMetric.dist a b = (a - b).natAbs := rfl

lemma zMetric_ball (f : ℤ) (n : ℕ) :
    zMetric.ball f n = Finset.Icc (f - (n : ℤ)) (f + (n : ℤ)) := rfl

/-- A radius-one ball has at most three edges. -/
lemma card_ball_one (f : ℤ) : (zMetric.ball f 1).card ≤ 3 := by
  have hb : zMetric.ball f 1 = Finset.Icc (f - 1) (f + 1) := by
    rw [zMetric_ball]
    norm_num
  rw [hb, Int.card_Icc]
  have h : f + 1 + 1 - (f - 1) = (3 : ℤ) := by ring
  rw [h]
  norm_num

/-- Every integer is within distance one of a multiple of three: the
three-periodic pivots `K`-cover the line with `K = 1`. -/
theorem cover_thirds : ∀ g : ℤ, ∃ k : ℤ, zMetric.dist (3 * k) g ≤ 1 := by
  intro g
  have hdecomp : 3 * (g / 3) + g % 3 = g := by omega
  have hr0 := Int.emod_nonneg g (by norm_num : (3 : ℤ) ≠ 0)
  have hr1 := Int.emod_lt_of_pos g (by norm_num : (0 : ℤ) < 3)
  have hcases : g % 3 = 0 ∨ g % 3 = 1 ∨ g % 3 = 2 := by omega
  rcases hcases with h | h | h
  · exact ⟨g / 3, by rw [zMetric_dist]; omega⟩
  · exact ⟨g / 3, by rw [zMetric_dist]; omega⟩
  · exact ⟨g / 3 + 1, by rw [zMetric_dist]; omega⟩

/-- Every radius-`n` ball has `2n + 1` edges, in particular at least `n + 1`:
the linear edge growth used by the density theorem. -/
lemma card_ball_le (f : ℤ) (n : ℕ) : n + 1 ≤ (zMetric.ball f n).card := by
  have hb : zMetric.ball f n = Finset.Icc (f - (n : ℤ)) (f + (n : ℤ)) := rfl
  rw [hb, Int.card_Icc]
  have h : f + (n : ℤ) + 1 - (f - (n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]
  omega

/-! ## Positive density of the concrete family -/

/-- **No finite set of three-periodic pivots covers the line.**  Quantitatively,
a finite pivot set whose radius-one balls cover every integer satisfies
`n + 1 ≤ 3 * |J|` for every `n`, hence is infinite. -/
theorem density_lower (J : Finset ℤ)
    (hcover : ∀ g : ℤ, ∃ k ∈ J, zMetric.dist (3 * k) g ≤ 1) (n : ℕ) :
    n + 1 ≤ 3 * J.card :=
  linear_growth_le_mul_card_devices zMetric J (p := fun k : ℤ => 3 * k) hcover
    (fun i => card_ball_one (3 * i)) (0 : ℤ) n (card_ball_le 0 n)

/-- **Quantitative device density for the infinite family.**  Around any edge
`f` and for every radius `n + 1`, at least `(n + 1)/3` of the three-periodic
devices have their pivot within that radius.  The device index set is infinite,
so the count is a `Set.ncard`. -/
theorem density_pivots (f : ℤ) (n : ℕ) :
    n + 1 ≤ 3 * (Set.ncard {k : ℤ | zMetric.dist f (3 * k) ≤ n + 1}) :=
  density_ncard zMetric (p := fun k : ℤ => 3 * k)
    (fun a b h => by
      have h' : 3 * a = 3 * b := h
      omega)
    cover_thirds (fun i => card_ball_one (3 * i)) f n (card_ball_le f n)

/-- The matching upper bound: devices whose pivots lie in the radius-`n` ball are
no more numerous than the ball.  (The pivots `3 * k` are distinct.) -/
theorem density_upper (J : Finset ℤ) (n : ℕ)
    (hJ : ∀ k ∈ J, zMetric.dist (0 : ℤ) (3 * k) ≤ n) :
    J.card ≤ (zMetric.ball (0 : ℤ) n).card :=
  card_le_card_ball zMetric J (fun a b h => by
    have : 3 * a = 3 * b := h
    omega) (0 : ℤ) n hJ

/-! ## The finite device windows and the activation tail -/

/-- The device window of radius `n`: the indices `-n, …, n`. -/
def devices (n : ℕ) : Finset ℤ :=
  (Finset.range (2 * n + 1)).map
    ⟨fun i : ℕ => (i : ℤ) - (n : ℤ), by
      intro a b h
      simp only at h
      omega⟩

lemma card_devices (n : ℕ) : (devices n).card = 2 * n + 1 := by
  rw [devices, Finset.card_map, Finset.card_range]

lemma devices_density (n : ℕ) : n + 1 ≤ 3 * (devices n).card := by
  rw [card_devices]
  omega

/-- **Concrete activation tail.**  With independent activation at rate `s` for
every device, the probability that all devices of the radius-`n` window are
inactive is at most `(1 - s)^{2n+1}`. -/
theorem activation_tail_le (s : unitInterval) (n : ℕ) :
    (FK.Configuration.bernoulliProduct (fun _ : ℤ => s) (allClosed (devices n))).toReal
      ≤ (1 - (s : ℝ)) ^ (devices n).card :=
  bernoulliProduct_allClosed_toReal_le (fun _ => s) (devices n) s
    (fun _ _ => le_rfl)

/-- **The tail is arbitrarily small** at every positive activation rate. -/
theorem activation_tail_eventually (s : unitInterval) (hs : 0 < (s : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, (FK.Configuration.bernoulliProduct (fun _ : ℤ => s)
      (allClosed (devices n))).toReal < ε := by
  obtain ⟨n, hn⟩ := exists_allClosed_le (J := devices) (D := 3) (by norm_num)
    devices_density hs hε
  exact ⟨n, (activation_tail_le s n).trans_lt hn⟩

end FK.AGPackingDensity.Example
