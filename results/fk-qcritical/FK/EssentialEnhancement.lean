import FK.Theorem14

/-!
# Essential enhancements from double rays

An edge is *essential* when there is a configuration in which opening it creates
an open double ray and closing it destroys every open double ray.  The
Aizenman--Grimmett step in the proof of Theorem 1.4 uses the fact that every edge
on a double ray has this property.  We prove that graph-theoretic implication by
opening exactly the edges of the given double ray.

This file does not state or assume the subsequent strict critical-point shift.
-/

open scoped Sym2

namespace FK.EssentialEnhancement

universe u

variable {V : Type u}

/-- A simple double ray, with its two infinite ends indexed by `ℤ`. -/
structure DoubleRay (G : SimpleGraph V) where
  vertex : ℤ → V
  vertex_injective : Function.Injective vertex
  adj (n : ℤ) : G.Adj (vertex n) (vertex (n + 1))

namespace DoubleRay

variable {G : SimpleGraph V}

/-- The edge joining two consecutive vertices of a double ray. -/
def edge (r : DoubleRay G) (n : ℤ) : G.edgeSet :=
  ⟨s(r.vertex n, r.vertex (n + 1)), r.adj n⟩

@[simp] theorem edge_val (r : DoubleRay G) (n : ℤ) :
    (r.edge n : Sym2 V) = s(r.vertex n, r.vertex (n + 1)) := rfl

/-- The configuration whose open edges are precisely those of `r`. -/
noncomputable def configuration (r : DoubleRay G) (e : G.edgeSet) : Bool := by
  classical
  exact decide (∃ n, r.edge n = e)

end DoubleRay

/-- Existence of an open simple double ray. -/
def HasOpenDoubleRay {G : SimpleGraph V} (ω : G.edgeSet → Bool) : Prop :=
  ∃ r : DoubleRay G, ∀ n, ω (r.edge n) = true

theorem HasOpenDoubleRay.mono {G : SimpleGraph V} {ω ξ : G.edgeSet → Bool}
    (hωξ : ω ≤ ξ) : HasOpenDoubleRay ω → HasOpenDoubleRay ξ := by
  rintro ⟨r, hr⟩
  refine ⟨r, fun n => ?_⟩
  have h := hωξ (r.edge n)
  rw [hr n] at h
  exact top_unique h

/-- Set one edge to a prescribed Boolean value.  The wrapper keeps the classical
`DecidableEq` instance out of every subsequent graph statement. -/
noncomputable def forceEdge {E : Type*} (ω : E → Bool) (e : E) (b : Bool) : E → Bool := by
  classical
  exact Function.update ω e b

@[simp] theorem forceEdge_same {E : Type*} (ω : E → Bool) (e : E) (b : Bool) :
    forceEdge ω e b e = b := by
  classical
  simp [forceEdge]

@[simp] theorem forceEdge_of_ne {E : Type*} (ω : E → Bool) {e e' : E}
    (h : e' ≠ e) (b : Bool) : forceEdge ω e b e' = ω e' := by
  classical
  simp [forceEdge, h]

/-- The Aizenman--Grimmett essentialness property, stated without assuming any
positivity or critical-point conclusion. -/
noncomputable def Essential {G : SimpleGraph V} (e : G.edgeSet) : Prop :=
  ∃ ω, HasOpenDoubleRay (forceEdge ω e true) ∧
    ¬ HasOpenDoubleRay (forceEdge ω e false)

/-- An edge is pivotal in the geometric sense required here when it belongs to
some double ray. -/
def OnDoubleRay {G : SimpleGraph V} (e : G.edgeSet) : Prop :=
  ∃ r : DoubleRay G, ∃ k, r.edge k = e

namespace IntegerRay

/-- An injective unit-step sequence has zero second difference.  In particular,
it cannot turn around at a point: turning would repeat a vertex. -/
theorem secondDifference_zero {f : ℤ → ℤ} (hf : Function.Injective f)
    (hstep : ∀ n, f (n + 1) = f n + 1 ∨ f (n + 1) = f n - 1) (n : ℤ) :
    f (n + 2) - f (n + 1) = f (n + 1) - f n := by
  have hne : f (n + 2) ≠ f n := by
    intro h
    have hn := hf h
    omega
  have h₀ := hstep n
  have h₁ := hstep (n + 1)
  rw [show n + 1 + 1 = n + 2 by ring] at h₁
  omega

/-- All oriented increments of an injective unit-step sequence are equal. -/
theorem step_eq_initial {f : ℤ → ℤ} (hf : Function.Injective f)
    (hstep : ∀ n, f (n + 1) = f n + 1 ∨ f (n + 1) = f n - 1) (n : ℤ) :
    f (n + 1) - f n = f 1 - f 0 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have h := secondDifference_zero hf hstep (n : ℤ)
      rw [show (n : ℤ) + 2 = (n : ℤ) + 1 + 1 by ring] at h
      exact h.trans ih
  | pred n ih =>
      have h := secondDifference_zero hf hstep (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring,
        show -(n : ℤ) - 1 + 2 = -(n : ℤ) + 1 by ring] at h
      simpa only [sub_add_cancel] using h.symm.trans ih

/-- An injective unit-step sequence on `ℤ` is affine with slope `±1`. -/
theorem affine {f : ℤ → ℤ} (hf : Function.Injective f)
    (hstep : ∀ n, f (n + 1) = f n + 1 ∨ f (n + 1) = f n - 1) (n : ℤ) :
    f n = f 0 + n * (f 1 - f 0) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have h := step_eq_initial hf hstep (n : ℤ)
      have hsucc : f ((n : ℤ) + 1) = f n + (f 1 - f 0) := by omega
      rw [hsucc, ih]
      ring
  | pred n ih =>
      have h := step_eq_initial hf hstep (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at h
      have hpred : f (-(n : ℤ) - 1) = f (-(n : ℤ)) - (f 1 - f 0) := by omega
      rw [hpred, ih]
      ring

/-- Every integer occurs in an injective unit-step sequence on `ℤ`. -/
theorem surjective {f : ℤ → ℤ} (hf : Function.Injective f)
    (hstep : ∀ n, f (n + 1) = f n + 1 ∨ f (n + 1) = f n - 1) :
    Function.Surjective f := by
  intro k
  have h₀ := hstep 0
  norm_num at h₀
  have ha := affine hf hstep
  rcases h₀ with h₀ | h₀
  · have hd : f 1 - f 0 = 1 := by omega
    refine ⟨k - f 0, ?_⟩
    rw [ha, hd]
    ring
  · have hd : f 1 - f 0 = -1 := by omega
    refine ⟨f 0 - k, ?_⟩
    rw [ha, hd]
    ring

end IntegerRay

@[simp] theorem configuration_edge {G : SimpleGraph V} (r : DoubleRay G) (n : ℤ) :
    r.configuration (r.edge n) = true := by
  classical
  simp [DoubleRay.configuration]

/-- Opening an edge of `r` in the configuration supported exactly on `r` makes
`r` an open double ray. -/
theorem hasOpenDoubleRay_update_configuration_true {G : SimpleGraph V}
    (r : DoubleRay G) {e : G.edgeSet} {k : ℤ} (_hk : r.edge k = e) :
    HasOpenDoubleRay (forceEdge r.configuration e true) := by
  refine ⟨r, fun n => ?_⟩
  by_cases h : r.edge n = e
  · simp [h]
  · rw [forceEdge_of_ne _ h]
    exact configuration_edge r n

/-- If `e` is an edge of `r`, then closing `e` in the configuration supported
exactly on `r` destroys every open double ray, not merely `r` itself.

The proof lifts any hypothetical second double ray to indices on `r`.  The lift
is an injective unit-step sequence, hence surjective by `IntegerRay.surjective`.
The surjectivity forces it to traverse the deleted edge, a contradiction. -/
theorem not_hasOpenDoubleRay_update_configuration_false {G : SimpleGraph V}
    (r : DoubleRay G) {e : G.edgeSet} {k : ℤ} (hk : r.edge k = e) :
    ¬ HasOpenDoubleRay (forceEdge r.configuration e false) := by
  rintro ⟨s, hs⟩
  have hsne (n : ℤ) : s.edge n ≠ e := by
    intro h
    have hn := hs n
    rw [h, forceEdge_same] at hn
    simp at hn
  have hsupport (n : ℤ) : ∃ i, r.edge i = s.edge n := by
    have hn := hs n
    rw [forceEdge_of_ne _ (hsne n)] at hn
    simpa only [DoubleRay.configuration, decide_eq_true_eq] using hn
  choose idx hidx using hsupport
  have hvertex (n : ℤ) : ∃ i, r.vertex i = s.vertex n := by
    have hp := congrArg Subtype.val (hidx n)
    change s(r.vertex (idx n), r.vertex (idx n + 1)) =
      s(s.vertex n, s.vertex (n + 1)) at hp
    have hm : s.vertex n ∈ s(r.vertex (idx n), r.vertex (idx n + 1)) := by
      rw [hp]
      simp
    rw [Sym2.mem_iff] at hm
    rcases hm with h | h
    · exact ⟨idx n, h.symm⟩
    · exact ⟨idx n + 1, h.symm⟩
  choose j hjvertex using hvertex
  have hjinj : Function.Injective j := by
    intro a b hab
    apply s.vertex_injective
    rw [← hjvertex a, ← hjvertex b, hab]
  have hpair (n : ℤ) :
      s(r.vertex (j n), r.vertex (j (n + 1))) =
        s(r.vertex (idx n), r.vertex (idx n + 1)) := by
    calc
      s(r.vertex (j n), r.vertex (j (n + 1))) =
          s(s.vertex n, s.vertex (n + 1)) := by rw [hjvertex n, hjvertex (n + 1)]
      _ = s(r.vertex (idx n), r.vertex (idx n + 1)) :=
        (congrArg Subtype.val (hidx n)).symm
  have hindex (n : ℤ) :
      (j n = idx n ∧ j (n + 1) = idx n + 1) ∨
        (j n = idx n + 1 ∧ j (n + 1) = idx n) := by
    rcases Sym2.eq_iff.mp (hpair n) with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · exact Or.inl ⟨r.vertex_injective h₀, r.vertex_injective h₁⟩
    · exact Or.inr ⟨r.vertex_injective h₀, r.vertex_injective h₁⟩
  have hstep (n : ℤ) : j (n + 1) = j n + 1 ∨ j (n + 1) = j n - 1 := by
    rcases hindex n with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · left
      omega
    · right
      omega
  obtain ⟨n, hn⟩ := IntegerRay.surjective hjinj hstep k
  have hfalse (m : ℤ) (heq : s.edge m = r.edge k) : False := by
    have hm := hs m
    rw [heq, hk, forceEdge_same] at hm
    simp at hm
  rcases hstep n with hnext | hnext
  · rcases hindex n with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · apply hfalse n
      have hi : idx n = k := by omega
      rw [← hidx n, hi]
    · omega
  · have hprevstep := IntegerRay.secondDifference_zero hjinj hstep (n - 1)
    rw [show n - 1 + 1 = n by ring, show n - 1 + 2 = n + 1 by ring] at hprevstep
    have hprev : j (n - 1) = k + 1 := by omega
    have hi := hindex (n - 1)
    rw [show n - 1 + 1 = n by ring] at hi
    rcases hi with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · omega
    · apply hfalse (n - 1)
      have hidxk : idx (n - 1) = k := by omega
      rw [← hidx (n - 1), hidxk]

/-- **Pivotal edges are essential.**  If an edge lies on a double ray, there is
an explicit configuration which has an open double ray when that edge is open
and has none when it is closed.  This is the geometric input to the
Aizenman--Grimmett theorem used in the proof of Theorem 1.4. -/
theorem essential_of_onDoubleRay {G : SimpleGraph V} {e : G.edgeSet}
    (he : OnDoubleRay e) : Essential e := by
  classical
  obtain ⟨r, k, hk⟩ := he
  exact ⟨r.configuration, hasOpenDoubleRay_update_configuration_true r hk,
    not_hasOpenDoubleRay_update_configuration_false r hk⟩

/-- Conversely, any edge whose opening can create a double ray whose closing
destroys all double rays must lie on a double ray.  Otherwise the witnessing
open ray would also survive with the edge closed. -/
theorem onDoubleRay_of_essential {G : SimpleGraph V} {e : G.edgeSet}
    (he : Essential e) : OnDoubleRay e := by
  obtain ⟨ω, ⟨r, hr⟩, hclosed⟩ := he
  by_contra h
  apply hclosed
  refine ⟨r, fun n => ?_⟩
  have hne : r.edge n ≠ e := by
    intro hn
    exact h ⟨r, n, hn⟩
  simpa only [forceEdge_of_ne _ hne] using hr n

/-- Essentialness is exactly the geometric double-ray property for a simple
graph. -/
theorem essential_iff_onDoubleRay {G : SimpleGraph V} (e : G.edgeSet) :
    Essential e ↔ OnDoubleRay e :=
  ⟨onDoubleRay_of_essential, essential_of_onDoubleRay⟩

/-- The essentialness conclusion uniformly over a set of enhanced edges. -/
theorem allEssential_of_forall_onDoubleRay {G : SimpleGraph V} {S : Set G.edgeSet}
    (h : ∀ e ∈ S, OnDoubleRay e) : ∀ e ∈ S, Essential e :=
  fun _ he => essential_of_onDoubleRay (h _ he)

/-- The preceding theorem in the exact shape of the `hstarEssential` and
`hcycleEssential` inputs to `FK.Theorem14.extended_phases_from_uniform_devices`.
The two window hypotheses required by that theorem are deliberately unchanged. -/
theorem theorem14_allEssential {G : SimpleGraph V} {S : Set G.edgeSet}
    (h : ∀ e ∈ S, OnDoubleRay e) :
    FK.Theorem14.AllEssential (fun e : G.edgeSet => Essential (G := G) e) S :=
  allEssential_of_forall_onDoubleRay h

end FK.EssentialEnhancement
