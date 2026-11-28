import BBR.Layers

/-!
# Definitions for the probabilistic step (Theorem 2.1) and for `p_c < 1`

Statement-level definitions shared by the files of `BBRAG`. No proofs.

* Claim 4 of [BBR] (Claim 5 without the hypothesis `α ∩ B_R(v) = ∅`).
* Finite boxes and the product Bernoulli weights of finite configurations; the crossing
  probability `tauF` as a finite weighted sum, its two "partial derivatives" `DpF`, `DsF`, and the
  expected numbers `ENp`, `ENs` of p-pivotal and s-pivotal sites.
* The abstract modification property `ModProp` (the finite-box form of Claim 4).
* `Adj2`/`Conn2` (adjacency at ℓ¹ distance 1 or 2) and `edgeCount`, for the Peierls argument.
-/

namespace BBR

open Classical

variable {d : ℕ}

/-! ### Claim 4 -/

/-- Claim 4 of [BBR] with explicit constants `L₀` and `R`: whenever `L ≥ L₀` and `v` is p-pivotal
for `R_L` in `(ω, α)`, some state `(ω', α')` differing from `(ω, α)` only within distance `R` of
`v` has an s-pivotal site `w` within distance `R` of `v`. -/
def Claim4With (E0 : Set (Site d) → Set (Site d)) (L₀ R : ℕ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L → ∀ (ω α : Set (Site d)) (v : Site d), PPivotal E0 L ω α v →
    ∃ ω' α' : Set (Site d),
      (∀ x, x ∉ ball v R → ((x ∈ ω' ↔ x ∈ ω) ∧ (x ∈ α' ↔ x ∈ α))) ∧
      ∃ w ∈ ball v R, SPivotal E0 L ω' α' w

/-- Claim 4 of [BBR]. -/
def Claim4 (E0 : Set (Site d) → Set (Site d)) : Prop := ∃ L₀ R : ℕ, Claim4With E0 L₀ R

/-! ### Finite boxes and weighted sums -/

/-- The ℓ¹ ball `B_N(0)` of `ℤ^d` as a finset. -/
noncomputable def boxFin (d N : ℕ) : Finset (Site d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(N : ℤ)) N).filter
    (fun x => x ∈ ball (0 : Site d) N)

section Weighted

variable {V : Type*} [DecidableEq V]

/-- The product Bernoulli(`p`) weight of the configuration `η ⊆ Λ` of the finite box `Λ`. -/
noncomputable def wt (Λ : Finset V) (p : ℝ) (η : Finset V) : ℝ :=
  ∏ x ∈ Λ, if x ∈ η then p else 1 - p

/-- `E_{p,s}[F]` for a function `F` of the two configurations `η, ζ ⊆ Λ` (independent
Bernoulli(`p`) and Bernoulli(`s`) configurations of `Λ`). For `F` the indicator of an event this
is its probability, a polynomial in `p` and `s`. -/
noncomputable def tauF (Λ : Finset V) (F : Finset V → Finset V → ℝ) (p s : ℝ) : ℝ :=
  ∑ η ∈ Λ.powerset, ∑ ζ ∈ Λ.powerset, F η ζ * wt Λ p η * wt Λ s ζ

/-- `∑_v E[F(η ∪ {v}, ζ) - F(η \ {v}, ζ)]`, the derivative of `tauF` in `p`
(Margulis–Russo). -/
noncomputable def DpF (Λ : Finset V) (F : Finset V → Finset V → ℝ) (p s : ℝ) : ℝ :=
  ∑ v ∈ Λ, ∑ η ∈ Λ.powerset, ∑ ζ ∈ Λ.powerset,
    (F (insert v η) ζ - F (η.erase v) ζ) * wt Λ p η * wt Λ s ζ

/-- `∑_w E[F(η, ζ ∪ {w}) - F(η, ζ \ {w})]`, the derivative of `tauF` in `s`. -/
noncomputable def DsF (Λ : Finset V) (F : Finset V → Finset V → ℝ) (p s : ℝ) : ℝ :=
  ∑ w ∈ Λ, ∑ η ∈ Λ.powerset, ∑ ζ ∈ Λ.powerset,
    (F η (insert w ζ) - F η (ζ.erase w)) * wt Λ p η * wt Λ s ζ

/-- The expected number of p-pivotal sites `E_{p,s} N_p` (for `F` the indicator of an event). -/
noncomputable def ENp (Λ : Finset V) (F : Finset V → Finset V → ℝ) (p s : ℝ) : ℝ :=
  ∑ v ∈ Λ, ∑ η ∈ Λ.powerset, ∑ ζ ∈ Λ.powerset,
    max (F (insert v η) ζ - F (η.erase v) ζ) 0 * wt Λ p η * wt Λ s ζ

/-- The expected number of s-pivotal sites `E_{p,s} N_s` (for `F` the indicator of an event). -/
noncomputable def ENs (Λ : Finset V) (F : Finset V → Finset V → ℝ) (p s : ℝ) : ℝ :=
  ∑ w ∈ Λ, ∑ η ∈ Λ.powerset, ∑ ζ ∈ Λ.powerset,
    max (F η (insert w ζ) - F η (ζ.erase w)) 0 * wt Λ p η * wt Λ s ζ

/-- The finite-box modification property (the form of Claim 4 used in the proof of [BBR, (2)]):
for every state `(η, ζ)` of `Λ` and every p-pivotal `v ∈ Λ`, some state `(η', ζ')` of `Λ` that
agrees with `(η, ζ)` outside `near v` has an s-pivotal site `w ∈ near v`. -/
def ModProp (Λ : Finset V) (F : Finset V → Finset V → ℝ) (near : V → Finset V) : Prop :=
  ∀ η ∈ Λ.powerset, ∀ ζ ∈ Λ.powerset, ∀ v ∈ Λ, F (insert v η) ζ = 1 → F (η.erase v) ζ = 0 →
    ∃ η' ∈ Λ.powerset, ∃ ζ' ∈ Λ.powerset, ∃ w ∈ near v,
      (∀ x ∈ Λ, x ∉ near v → ((x ∈ η' ↔ x ∈ η) ∧ (x ∈ ζ' ↔ x ∈ ζ))) ∧
      F η' (insert w ζ') = 1 ∧ F η' (ζ'.erase w) = 0

end Weighted

open Classical in
/-- The indicator of the crossing event `R_L` (the enhanced configuration contains a path from `0`
to `S_L`) for finite configurations `η` (open sites) and `ζ` (activation sites). -/
noncomputable def RLind (E0 : Set (Site d) → Set (Site d)) (L : ℕ) (η ζ : Finset (Site d)) : ℝ :=
  if Crosses L (enhanced E0 ↑η ↑ζ) then 1 else 0

/-! ### Adjacency at distance at most two, and edge counts of walks -/

/-- Sites at ℓ¹ distance 1 or 2. -/
def Adj2 (x y : Site d) : Prop := 1 ≤ dist1 x y ∧ dist1 x y ≤ 2

/-- `S` is connected for `Adj2`: any two of its sites are joined by an `Adj2`-walk inside `S`. -/
def Conn2 (S : Set (Site d)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ P : List (Site d), P.head? = some x ∧ P.getLast? = some y ∧
    P.IsChain Adj2 ∧ ∀ z ∈ P, z ∈ S

/-- The number of steps `(x, y)` of the walk `P` with `e x y`. -/
def edgeCount (e : Site d → Site d → Prop) [DecidableRel e] : List (Site d) → ℕ
  | x :: y :: t => (if e x y then 1 else 0) + edgeCount e (y :: t)
  | _ => 0

end BBR
