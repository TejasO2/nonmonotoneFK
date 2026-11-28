import Mathlib

/-!
# Definitions

Lean formalization of "Essential enhancements of site percolation in every dimension".
This file fixes the combinatorial definitions used in the statements (the probabilistic ones are in
`BBR/Main.lean`); it contains no proofs. Section and result numbers refer to the paper; [BBR] is
Balister, Bollobás and Riordan, "Essential enhancements revisited".

Notation (§1.5): `|x| = ∑ |x_i|` is the ℓ¹ norm, `B_r(c)` and `S_r(c)` are ℓ¹ balls and spheres, two
sites are adjacent if `|x - y| = 1`, `U = {±e_1, …, ±e_d}`, and `π, δ ∈ U` are orthogonal if `δ ≠ ±π`.
A *path* is a finite sequence of distinct sites in which consecutive sites are adjacent; it is
*induced* if no two non-consecutive sites are adjacent. A set *contains a path* from `x` to `y` if
some path from `x` to `y` has all its sites in the set.
-/

namespace BBR

/-- The sites of `ℤ^d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

variable {d : ℕ}

/-- The ℓ¹ norm `|x| = ∑ᵢ |xᵢ|`. -/
def norm1 (x : Site d) : ℤ := ∑ i, |x i|

/-- The ℓ¹ distance `|x - y|`. -/
def dist1 (x y : Site d) : ℤ := norm1 (x - y)

/-- The ℓ¹ ball `B_r(c) = {x : |x - c| ≤ r}`. -/
def ball (c : Site d) (r : ℤ) : Set (Site d) := {x | dist1 x c ≤ r}

/-- The ℓ¹ sphere `S_r(c) = {x : |x - c| = r}`. -/
def sphere (c : Site d) (r : ℤ) : Set (Site d) := {x | dist1 x c = r}

/-- Two sites are adjacent if `|x - y| = 1`. -/
def Adj (x y : Site d) : Prop := dist1 x y = 1

/-- `u` is a signed unit vector, `u ∈ U = {±e_1, …, ±e_d}`. -/
def IsUnitVec (u : Site d) : Prop := norm1 u = 1

/-- Signed unit vectors `π, δ` are orthogonal if `δ ≠ ±π`. -/
def Orth (π δ : Site d) : Prop := δ ≠ π ∧ δ ≠ -π

/-- The first coordinate vector `e_1` (so `m • e1` is the site `m e_1 = (m, 0, …, 0)`). -/
def e1 : Site d := fun i => if (i : ℕ) = 0 then 1 else 0

/-! ### Walks and paths -/

/-- A walk: a nonempty finite sequence of sites in which consecutive sites are adjacent. -/
def IsWalk (P : List (Site d)) : Prop := P ≠ [] ∧ P.IsChain Adj

/-- A path: a walk whose sites are distinct. -/
def IsPath (P : List (Site d)) : Prop := IsWalk P ∧ P.Nodup

/-- An induced path: a path in which no two non-consecutive sites are adjacent. -/
def IsInducedPath (P : List (Site d)) : Prop :=
  IsPath P ∧ ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length), i + 1 < j → ¬ Adj P[i] P[j]

/-- `A` contains a path from `x` to `y`. -/
def ContainsPath (A : Set (Site d)) (x y : Site d) : Prop :=
  ∃ P : List (Site d), IsPath P ∧ P.head? = some x ∧ P.getLast? = some y ∧ ∀ z ∈ P, z ∈ A

/-- `A` is connected: it contains a path between any two of its sites. -/
def SiteConnected (A : Set (Site d)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ContainsPath A x y

/-- `A` contains a doubly infinite path. -/
def HasBiInfPath (A : Set (Site d)) : Prop :=
  ∃ f : ℤ → Site d, Function.Injective f ∧ (∀ n, Adj (f n) (f (n + 1))) ∧ ∀ n, f n ∈ A

/-! ### Enhancements (§1.1, §2.1) -/

/-- The translate `A + v` of a configuration. -/
def translate (A : Set (Site d)) (v : Site d) : Set (Site d) := (fun x => x + v) '' A

/-- `E0` has range `r`: `E0 ω` depends only on `ω ∩ B_r`, and `E0 ω ⊆ B_r`. -/
def HasRange (E0 : Set (Site d) → Set (Site d)) (r : ℤ) : Prop :=
  (∀ ω ω' : Set (Site d), ω ∩ ball 0 r = ω' ∩ ball 0 r → E0 ω = E0 ω') ∧
    ∀ ω : Set (Site d), E0 ω ⊆ ball 0 r

/-- An enhancement: a map `E0 : 𝒫(ℤ^d) → 𝒫(ℤ^d)` with some finite range. -/
def IsEnhancement (E0 : Set (Site d) → Set (Site d)) : Prop := ∃ r : ℕ, HasRange E0 r

/-- The enhanced configuration `E(ω, α) = ω ∪ ⋃_{v ∈ α} (E0(ω - v) + v)`. -/
def enhanced (E0 : Set (Site d) → Set (Site d)) (ω α : Set (Site d)) : Set (Site d) :=
  ω ∪ ⋃ v ∈ α, translate (E0 (translate ω (-v))) v

/-- `E0` is essential: some `ω` contains no doubly infinite path while `ω ∪ E0 ω` does. -/
def IsEssential (E0 : Set (Site d) → Set (Site d)) : Prop :=
  ∃ ω : Set (Site d), ¬ HasBiInfPath ω ∧ HasBiInfPath (ω ∪ E0 ω)

/-- The crossing event `R_L` for a configuration `A`: `A` contains a path from `0` to `S_L`. -/
def Crosses (L : ℕ) (A : Set (Site d)) : Prop :=
  ∃ y ∈ sphere (0 : Site d) L, ContainsPath A 0 y

/-- `v` is p-pivotal for `R_L` in the state `(ω, α)`. -/
def PPivotal (E0 : Set (Site d) → Set (Site d)) (L : ℕ) (ω α : Set (Site d)) (v : Site d) : Prop :=
  Crosses L (enhanced E0 (insert v ω) α) ∧ ¬ Crosses L (enhanced E0 (ω \ {v}) α)

/-- `v` is s-pivotal for `R_L` in the state `(ω, α)`. -/
def SPivotal (E0 : Set (Site d) → Set (Site d)) (L : ℕ) (ω α : Set (Site d)) (v : Site d) : Prop :=
  Crosses L (enhanced E0 ω (insert v α)) ∧ ¬ Crosses L (enhanced E0 ω (α \ {v}))

/-- **Claim 5** of [BBR] (§2.1): there are constants `L₀, R` (depending only on `E0`) such that
whenever `L ≥ L₀`, `v` is p-pivotal for `R_L` in `(ω, α)` and `α ∩ B_R(v) = ∅`, there is a state
`(ω', α')` differing from `(ω, α)` only within distance `R` of `v` and a site `w` within distance `R`
of `v` that is s-pivotal for `R_L` in `(ω', α')`. -/
def Claim5 (E0 : Set (Site d) → Set (Site d)) : Prop :=
  ∃ L₀ R : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ (ω α : Set (Site d)) (v : Site d),
    PPivotal E0 L ω α v → α ∩ ball v R = ∅ →
    ∃ ω' α' : Set (Site d),
      (∀ x, x ∉ ball v R → ((x ∈ ω' ↔ x ∈ ω) ∧ (x ∈ α' ↔ x ∈ α))) ∧
      ∃ w ∈ ball v R, SPivotal E0 L ω' α' w

/-! ### Corner pairs, separated pairs, ports (§2.6, §2.7) -/

/-- A corner pair of `S_ρ(c)`: the set `{x, y}` equals `{c + ρπ, c + (ρ-1)π + δ}` for orthogonal
`π, δ ∈ U` (Definition 2.11(1)). -/
def IsCornerPair (c : Site d) (ρ : ℤ) (x y : Site d) : Prop :=
  ∃ π δ : Site d, IsUnitVec π ∧ IsUnitVec δ ∧ Orth π δ ∧
    ((x = c + ρ • π ∧ y = c + (ρ - 1) • π + δ) ∨ (y = c + ρ • π ∧ x = c + (ρ - 1) • π + δ))

/-- `x, y` are separated in `S_ρ(c)`: for some coordinate `i` there is an integer `s` with
`|s| ≤ ρ - 5` strictly between `x_i - c_i` and `y_i - c_i` (Definition 2.11(2)). -/
def Separated (c : Site d) (ρ : ℤ) (x y : Site d) : Prop :=
  ∃ (i : Fin d) (s : ℤ), |s| ≤ ρ - 5 ∧
    ((x i - c i < s ∧ s < y i - c i) ∨ (y i - c i < s ∧ s < x i - c i))

/-- `a` is the first site of the sequence `P` in `D`. -/
def IsFirstIn (P : List (Site d)) (D : Set (Site d)) (a : Site d) : Prop :=
  ∃ (i : ℕ) (hi : i < P.length), P[i] = a ∧ a ∈ D ∧
    ∀ (j : ℕ) (hj : j < i), P[j]'(Nat.lt_trans hj hi) ∉ D

/-- `g` is the last site of the sequence `P` in `D`. -/
def IsLastIn (P : List (Site d)) (D : Set (Site d)) (g : Site d) : Prop :=
  ∃ (i : ℕ) (hi : i < P.length), P[i] = g ∧ g ∈ D ∧
    ∀ (j : ℕ) (hj : j < P.length), i < j → P[j] ∉ D

/-- The number of sites of `P` in `D`, `|P ∩ D|`. -/
noncomputable def countIn (P : List (Site d)) (D : Set (Site d)) : ℕ :=
  Set.ncard {x | x ∈ P ∧ x ∈ D}

/-- The property of `K` in the Corner Lemma CL(d) for a given `ρ₀`: for every induced path `P`
(ordered from one end to the other) through `v` whose two end sites lie outside `B_K(v)`, there is a
ball `B_ρ(c)` with `ρ ≥ ρ₀`, `B_{ρ+1}(c) ⊆ B_K(v)` and `|P ∩ B_ρ(c)| ≥ 3` such that the first and
the last site of `P` in `B_ρ(c)` do not form a corner pair of `S_ρ(c)`. -/
def CLProperty (d : ℕ) (ρ₀ K : ℕ) : Prop :=
  ∀ (P : List (Site d)) (v : Site d), IsInducedPath P → v ∈ P →
    (∀ x ∈ P.head?, x ∉ ball v K) → (∀ x ∈ P.getLast?, x ∉ ball v K) →
    ∃ (c : Site d) (ρ : ℕ), ρ₀ ≤ ρ ∧ ball c ((ρ : ℤ) + 1) ⊆ ball v K ∧
      3 ≤ countIn P (ball c ρ) ∧
      ∃ a g : Site d, IsFirstIn P (ball c ρ) a ∧ IsLastIn P (ball c ρ) g ∧ ¬ IsCornerPair c ρ a g

/-- **Corner Lemma CL(d)** (§2.7): for every integer `ρ₀ ≥ 2` there is `K = K(d, ρ₀)` with the
property `CLProperty d ρ₀ K`. -/
def CornerLemma (d : ℕ) : Prop := ∀ ρ₀ : ℕ, 2 ≤ ρ₀ → ∃ K : ℕ, CLProperty d ρ₀ K

/-! ### Gadgets and designs (§2.3, §2.6) -/

/-- The conclusions of Lemma 2.2 (the gadget) for `E0` of range `rE`: `m > rE`, `ω_g ⊆ B_m`,
`ω_g ∩ S_m = {m e_1, -m e_1}`, `ω_g` contains no path from `-m e_1` to `m e_1`, and
`ω_g ∪ E0(ω_g)` contains such a path. -/
def IsGadget (E0 : Set (Site d) → Set (Site d)) (rE m : ℕ) (ωg : Set (Site d)) : Prop :=
  rE < m ∧ ωg ⊆ ball 0 m ∧ ωg ∩ sphere 0 m = {(m : ℤ) • e1, -((m : ℤ) • e1)} ∧
    ¬ ContainsPath ωg (-((m : ℤ) • e1)) ((m : ℤ) • e1) ∧
    ContainsPath (ωg ∪ E0 ωg) (-((m : ℤ) • e1)) ((m : ℤ) • e1)

/-- Conditions (D1)–(D4) of Definition 2.9 on a red set `R` and a green set `G` inside `D = B_ρ(c)`,
for the ports `a, g` and the gadget size `m`. The interior design is then `R ∪ G ∪ (ω_g + c)`. -/
def IsDesignRG (c : Site d) (ρ m : ℤ) (a g : Site d) (R G : Set (Site d)) : Prop :=
  R ⊆ ball c ρ ∧ G ⊆ ball c ρ ∧
  -- (D1)
  a ∈ R ∧ g ∈ G ∧ SiteConnected R ∧ SiteConnected G ∧
  -- (D2)
  (∀ x ∈ R, x ≠ a → x ∈ ball c (ρ - 1)) ∧ (∀ x ∈ G, x ≠ g → x ∈ ball c (ρ - 1)) ∧
  -- (D3)
  ((R ∩ ball c m = {c + m • e1} ∧ G ∩ ball c m = {c - m • e1}) ∨
    (R ∩ ball c m = {c - m • e1} ∧ G ∩ ball c m = {c + m • e1})) ∧
  -- (D4)
  (∀ x ∈ R, ∀ y ∈ G, x ≠ y ∧ ¬ Adj x y)

end BBR
