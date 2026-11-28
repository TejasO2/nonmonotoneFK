import FK.StaircaseConnected
import FK.AGShift
import FK.PcPos
import FK.AGDeviceEssentiality
import BBRAG.Peierls

/-!
# An independent bond-star enhancement on the square lattice

This is a deliberately scoped special case, not a proof of the general
Aizenman--Grimmett rerouting theorem.  A device at each lattice vertex opens
its incident bonds.  Bonds and devices have independent Boolean coordinates.
Even-indexed active centres give a coarse independent site-percolation model;
two adjacent active centres are connected through their midpoint.  BBR's
Peierls bound supplies a nondegenerate activation rate at which this coarse
model percolates.  The ordinary bond model is separately subcritical at the
explicit positive rate `1/8` by the FK first-moment bound.
-/

open Set MeasureTheory ProbabilityTheory
open CurvatureVariance.Infra.Percolation
open scoped Sym2 ENNReal unitInterval

namespace FK.SquareLatticeStar

open FK.PlaneTopology.GridFrontier
open FK.InfiniteVolume.ConventionGeometry
open FK.EssentialEnhancement
open FK.AGImplant

noncomputable section

/-- The square-lattice origin, also viewed as the centre of its star. -/
def origin : GridV := (0, 0)

/-- The vertices adjacent to a given square-lattice vertex. -/
def neighbours (v : GridV) : Set GridV :=
  {(v.1 + 1, v.2), (v.1 - 1, v.2), (v.1, v.2 + 1), (v.1, v.2 - 1)}

lemma neighbours_finite (v : GridV) : (neighbours v).Finite := by
  simp [neighbours]

lemma neighborSet_subset_neighbours (v : GridV) : gridGraph.neighborSet v ⊆ neighbours v := by
  intro w hw
  change gridAdj v w at hw
  rcases hw with ⟨hxy, hy | hy⟩ | ⟨hxy, hx | hx⟩
  · have h : w = (v.1, v.2 - 1) := Prod.ext hxy.symm (by omega)
    simp [neighbours, h]
  · have h : w = (v.1, v.2 + 1) := Prod.ext hxy.symm (by omega)
    simp [neighbours, h]
  · have h : w = (v.1 - 1, v.2) := Prod.ext (by omega) hxy.symm
    simp [neighbours, h]
  · have h : w = (v.1 + 1, v.2) := Prod.ext (by omega) hxy.symm
    simp [neighbours, h]

lemma neighborSet_finite (v : GridV) : (gridGraph.neighborSet v).Finite :=
  (neighbours_finite v).subset (neighborSet_subset_neighbours v)

instance : gridGraph.LocallyFinite := fun v => (neighborSet_finite v).fintype

lemma neighborSet_ncard_le_four (v : GridV) : (gridGraph.neighborSet v).ncard ≤ 4 := by
  calc
    (gridGraph.neighborSet v).ncard ≤ (neighbours v).ncard :=
      Set.ncard_le_ncard (neighborSet_subset_neighbours v) (neighbours_finite v)
    _ ≤ 4 := by
      have h1 := Set.ncard_insert_le (v.1 + 1, v.2)
        ({(v.1 - 1, v.2), (v.1, v.2 + 1), (v.1, v.2 - 1)} : Set GridV)
      have h2 := Set.ncard_insert_le (v.1 - 1, v.2)
        ({(v.1, v.2 + 1), (v.1, v.2 - 1)} : Set GridV)
      have h3 := Set.ncard_insert_le (v.1, v.2 + 1) ({(v.1, v.2 - 1)} : Set GridV)
      simp only [neighbours, Set.ncard_singleton] at *
      omega

/-- Connectedness of the actual square lattice, extracted from an explicit open
walk in the staircase configuration. -/
theorem grid_connected : gridGraph.Connected := by
  apply gridGraph.connected_iff_exists_forall_reachable.2
  refine ⟨origin, fun v => ?_⟩
  obtain ⟨w, _⟩ := openConnected_symm
    (FK.PlaneTopology.StaircaseConnected.staircase_connected v)
  exact ⟨w⟩

/-- A positive ordinary bond parameter with zero percolation at the origin. -/
def baseRate : unitInterval := ⟨1 / 8, by norm_num, by norm_num⟩

lemma baseRate_pos : (0 : ℝ) < (baseRate : ℝ) := by norm_num [baseRate]

lemma baseRate_mul_four_lt_one : (baseRate : ℝ) * 4 < 1 := by norm_num [baseRate]

theorem base_nonpercolating : percolationProb gridGraph origin baseRate = 0 :=
  percolationProb_eq_zero_of_mul_card_lt_one grid_connected neighborSet_ncard_le_four
    (by simpa using baseRate_mul_four_lt_one)

/-- The usual horizontal double ray in the square lattice. -/
def axisDoubleRay : DoubleRay gridGraph where
  vertex n := (n, 0)
  vertex_injective := by
    intro m n h
    exact congrArg Prod.fst h
  adj n := gridAdj_fst_add n 0

/-- A star support is exactly the set of bonds incident with its centre. -/
def starSupport (v : GridV) : Set gridGraph.edgeSet := {e | v ∈ (e : Sym2 GridV)}

lemma origin_mem_axis_edge_zero : origin ∈ (axisDoubleRay.edge 0 : Sym2 GridV) := by
  exact Sym2.mem_mk_left _ _

/-- One independent square-lattice star is essential in the actual shared-
activation double-ray sense of `FK.AGImplant`. -/
theorem originStar_essential : DeviceEssential gridGraph starSupport origin := by
  apply deviceEssential_of_onDoubleRay starSupport origin origin_mem_axis_edge_zero
  exact ⟨axisDoubleRay, 0, rfl⟩

/-- Coarse sites are mapped to the even sublattice of square-lattice centres. -/
def coarse (x : BBR.Site 2) : GridV := (2 * x 0, 2 * x 1)

lemma coarse_injective : Function.Injective coarse := by
  intro x y h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  change 2 * x 0 = 2 * y 0 at h0
  change 2 * x 1 = 2 * y 1 at h1
  funext i
  fin_cases i
  · change x 0 = y 0
    omega
  · change x 1 = y 1
    omega

lemma coarse_zero : coarse 0 = origin := by
  simp [coarse, origin]

/-- The independent law on ordinary bonds together with all star devices. -/
noncomputable def starLaw (p s : unitInterval) :
    Measure (FK.AGPeeling.JointConfig gridGraph.edgeSet GridV) :=
  FKLimit.bernoulliProduct (Sum.elim (fun _ : gridGraph.edgeSet => p) (fun _ : GridV => s))

/-- The enhanced root-percolation event for the independent bond-star model. -/
def EnhancedRootEvent : Set (FK.AGPeeling.JointConfig gridGraph.edgeSet GridV) :=
  deviceEvent starSupport (FK.AGShift.RootPercolating gridGraph origin)

/-- The active even centres, viewed as a site configuration on `BBR.Site 2`. -/
def coarseActive (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV) : Set (BBR.Site 2) :=
  {x | χ (Sum.inr (coarse x)) = true}

/-- The bond on the left side of a star centre is open whenever that centre is
active. -/
lemma device_open_left (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV)
    {v w : GridV} (h : gridGraph.Adj v w) (hv : χ (Sum.inr v) = true) :
    deviceConfig starSupport χ ⟨s(v, w), h⟩ = true := by
  apply deviceConfig_eq_true_of_mem starSupport χ v _ hv
  exact Sym2.mem_mk_left _ _

/-- The corresponding fact with the star centre on the right. -/
lemma device_open_right (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV)
    {v w : GridV} (h : gridGraph.Adj v w) (hw : χ (Sum.inr w) = true) :
    deviceConfig starSupport χ ⟨s(v, w), h⟩ = true := by
  apply deviceConfig_eq_true_of_mem starSupport χ w _ hw
  exact Sym2.mem_mk_right _ _

lemma coarse_add_single_zero_pos (x : BBR.Site 2) :
    coarse (x + Pi.single (0 : Fin 2) 1) = ((2 * x 0 + 1) + 1, 2 * x 1) := by
  apply Prod.ext <;> simp [coarse] <;> ring

lemma coarse_add_single_zero_neg (x : BBR.Site 2) :
    coarse (x + Pi.single (0 : Fin 2) (-1)) = ((2 * x 0 - 1) - 1, 2 * x 1) := by
  apply Prod.ext <;> simp [coarse] <;> ring

lemma coarse_add_single_one_pos (x : BBR.Site 2) :
    coarse (x + Pi.single (1 : Fin 2) 1) = (2 * x 0, (2 * x 1 + 1) + 1) := by
  apply Prod.ext <;> simp [coarse] <;> ring

lemma coarse_add_single_one_neg (x : BBR.Site 2) :
    coarse (x + Pi.single (1 : Fin 2) (-1)) = (2 * x 0, (2 * x 1 - 1) - 1) := by
  apply Prod.ext <;> simp [coarse] <;> ring

/-- Two adjacent active coarse centres are joined by two enhanced bonds through
their midpoint. -/
lemma coarse_adj_openConnected (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV)
    {x y : BBR.Site 2} (hxy : BBR.Adj x y)
    (hx : χ (Sum.inr (coarse x)) = true) (hy : χ (Sum.inr (coarse y)) = true) :
    OpenConnected gridGraph (deviceConfig starSupport χ) Set.univ (coarse x) (coarse y) := by
  obtain ⟨u, hu, rfl⟩ := (BBR.adj_iff_exists_unitVec x y).mp hxy
  obtain ⟨i, t, ht, rfl⟩ := (BBR.isUnitVec_iff u).mp hu
  fin_cases i
  · rcases ht with rfl | rfl
    · let m : GridV := (2 * x 0 + 1, 2 * x 1)
      have hleft : gridGraph.Adj (coarse x) m := by
        exact gridAdj_fst_add (2 * x 0) (2 * x 1)
      have hright : gridGraph.Adj m (coarse (x + Pi.single (0 : Fin 2) 1)) := by
        rw [coarse_add_single_zero_pos]
        exact gridAdj_fst_add (2 * x 0 + 1) (2 * x 1)
      exact (OpenConnected.of_adj hleft (Set.mem_univ _) (device_open_left χ hleft hx)).trans
        (OpenConnected.of_adj hright (Set.mem_univ _) (device_open_right χ hright hy))
    · let m : GridV := (2 * x 0 - 1, 2 * x 1)
      have hleft : gridGraph.Adj (coarse x) m := by
        have h := gridAdj_symm (gridAdj_fst_add (2 * x 0 - 1) (2 * x 1))
        rw [show 2 * x 0 - 1 + 1 = 2 * x 0 by ring] at h
        change gridAdj (2 * x 0, 2 * x 1) m
        exact h
      have hright : gridGraph.Adj m (coarse (x + Pi.single (0 : Fin 2) (-1))) := by
        rw [coarse_add_single_zero_neg]
        have h := gridAdj_symm (gridAdj_fst_add ((2 * x 0 - 1) - 1) (2 * x 1))
        rw [show (2 * x 0 - 1) - 1 + 1 = 2 * x 0 - 1 by ring] at h
        change gridAdj m ((2 * x 0 - 1) - 1, 2 * x 1)
        exact h
      exact (OpenConnected.of_adj hleft (Set.mem_univ _) (device_open_left χ hleft hx)).trans
        (OpenConnected.of_adj hright (Set.mem_univ _) (device_open_right χ hright hy))
  · rcases ht with rfl | rfl
    · let m : GridV := (2 * x 0, 2 * x 1 + 1)
      have hleft : gridGraph.Adj (coarse x) m := by
        exact gridAdj_snd_add (2 * x 0) (2 * x 1)
      have hright : gridGraph.Adj m (coarse (x + Pi.single (1 : Fin 2) 1)) := by
        rw [coarse_add_single_one_pos]
        exact gridAdj_snd_add (2 * x 0) (2 * x 1 + 1)
      exact (OpenConnected.of_adj hleft (Set.mem_univ _) (device_open_left χ hleft hx)).trans
        (OpenConnected.of_adj hright (Set.mem_univ _) (device_open_right χ hright hy))
    · let m : GridV := (2 * x 0, 2 * x 1 - 1)
      have hleft : gridGraph.Adj (coarse x) m := by
        have h := gridAdj_symm (gridAdj_snd_add (2 * x 0) (2 * x 1 - 1))
        rw [show 2 * x 1 - 1 + 1 = 2 * x 1 by ring] at h
        change gridAdj (2 * x 0, 2 * x 1) m
        exact h
      have hright : gridGraph.Adj m (coarse (x + Pi.single (1 : Fin 2) (-1))) := by
        rw [coarse_add_single_one_neg]
        have h := gridAdj_symm (gridAdj_snd_add (2 * x 0) ((2 * x 1 - 1) - 1))
        rw [show (2 * x 1 - 1) - 1 + 1 = 2 * x 1 - 1 by ring] at h
        change gridAdj m (2 * x 0, (2 * x 1 - 1) - 1)
        exact h
      exact (OpenConnected.of_adj hleft (Set.mem_univ _) (device_open_left χ hleft hx)).trans
        (OpenConnected.of_adj hright (Set.mem_univ _) (device_open_right χ hright hy))

/-- Every path in the active coarse configuration becomes an open enhanced
walk between the corresponding even lattice centres. -/
lemma coarse_openConnected_of_containsPath (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV)
    {x y : BBR.Site 2} (h : BBR.ContainsPath (coarseActive χ) x y) :
    OpenConnected gridGraph (deviceConfig starSupport χ) Set.univ (coarse x) (coarse y) := by
  obtain ⟨P, hP, hx, hy, hA⟩ := h
  induction P generalizing x with
  | nil => simp at hx
  | cons a t ih =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst a
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hy
      subst y
      exact OpenConnected.refl _ _ _
    | cons b t =>
      simp only [List.getLast?_cons_cons] at hy
      have hxb : BBR.Adj x b := hP.1.2.rel
      have hfirst := coarse_adj_openConnected χ hxb
        (hA x List.mem_cons_self) (hA b (List.mem_cons_of_mem _ List.mem_cons_self))
      apply hfirst.trans
      apply ih (x := b)
        ⟨⟨List.cons_ne_nil _ _, hP.1.2.of_cons⟩, hP.2.of_cons⟩ rfl hy
      intro z hz
      exact hA z (List.mem_cons_of_mem _ hz)

/-- An infinite active coarse cluster at zero is contained, after applying
`coarse`, in the enhanced square-lattice cluster at the origin. -/
lemma root_of_coarse_infinite (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV)
    (h : BBR.OriginInInfiniteCluster (coarseActive χ)) : χ ∈ EnhancedRootEvent := by
  change {v | OpenConnected gridGraph (deviceConfig starSupport χ) Set.univ origin v}.Infinite
  change {x | BBR.ContainsPath (coarseActive χ) 0 x}.Infinite at h
  have himage : (coarse '' {x | BBR.ContainsPath (coarseActive χ) 0 x}).Infinite :=
    h.image (fun a _ b _ hab => coarse_injective hab)
  apply Set.Infinite.mono (s := coarse '' {x | BBR.ContainsPath (coarseActive χ) 0 x})
    (t := {v | OpenConnected gridGraph (deviceConfig starSupport χ) Set.univ origin v}) ?_ himage
  rintro v ⟨x, hx, rfl⟩
  rw [← coarse_zero]
  exact coarse_openConnected_of_containsPath χ hx

/-- Membership in a fixed path is a finite-cylinder condition. -/
lemma measurableSet_containsPath (x y : BBR.Site 2) :
    MeasurableSet {A : Set (BBR.Site 2) | BBR.ContainsPath A x y} := by
  classical
  unfold BBR.ContainsPath
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun (P : List (BBR.Site 2)) => ?_
  by_cases hP : BBR.IsPath P ∧ P.head? = some x ∧ P.getLast? = some y
  · simp only [hP, true_and]
    have hset : {A : Set (BBR.Site 2) | ∀ z ∈ P, z ∈ A} =
        ⋂ z ∈ P.toFinset, {A : Set (BBR.Site 2) | z ∈ A} := by
      ext A
      simp
    rw [hset]
    exact Finset.measurableSet_biInter P.toFinset fun z _ => measurableSet_mem z
  · have hset : {A : Set (BBR.Site 2) |
        (BBR.IsPath P ∧ P.head? = some x ∧ P.getLast? = some y ∧ ∀ z ∈ P, z ∈ A)} = ∅ := by
      ext A
      constructor
      · intro h
        exact (hP ⟨h.1, h.2.1, h.2.2.1⟩).elim
      · intro h
        exact h.elim
    rw [hset]
    exact MeasurableSet.empty

lemma measurableSet_originInfinite :
    MeasurableSet {A : Set (BBR.Site 2) | BBR.OriginInInfiniteCluster A} := by
  apply MeasurableSet.setOfPred_infinite.preimage
  exact measurable_set_iff.mpr fun x => by
    rw [← measurableSet_setOfPred]
    exact measurableSet_containsPath 0 x

lemma measurable_coarseActive : Measurable coarseActive := by
  change Measurable (fun (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV) =>
    openSet (fun x : BBR.Site 2 => χ (Sum.inr (coarse x))))
  apply measurable_openSet.comp
  exact measurable_pi_iff.2 fun x =>
    measurable_pi_apply (X := fun _ : gridGraph.edgeSet ⊕ GridV => Bool) (Sum.inr (coarse x))

/-- The even-centre marginal of the independent joint bond/star law is exactly
BBR's independent site law. -/
theorem map_coarseActive_starLaw (p s : unitInterval) :
    Measure.map coarseActive (starLaw p s) = BBR.sitePerc 2 s := by
  have hinj : Function.Injective
      (fun x : BBR.Site 2 => (Sum.inr (coarse x) : gridGraph.edgeSet ⊕ GridV)) :=
    fun _ _ h => coarse_injective (Sum.inr.inj h)
  have hrestrict : Measurable
      (fun (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV) (x : BBR.Site 2) =>
        χ (Sum.inr (coarse x))) :=
    measurable_pi_iff.2 fun x =>
      measurable_pi_apply (X := fun _ : gridGraph.edgeSet ⊕ GridV => Bool) (Sum.inr (coarse x))
  have hcomp : coarseActive = openSet ∘
      (fun (χ : FK.AGPeeling.JointConfig gridGraph.edgeSet GridV) (x : BBR.Site 2) =>
        χ (Sum.inr (coarse x))) := rfl
  have hprod : starLaw p s =
      Measure.infinitePi (fun z : gridGraph.edgeSet ⊕ GridV =>
        bernoulliMeasure true false (Sum.elim (fun _ : gridGraph.edgeSet => p) (fun _ : GridV => s) z)) := rfl
  rw [hcomp, ← Measure.map_map measurable_openSet hrestrict, hprod,
    Measure.map_infinitePi_infinitePi_of_inj hinj]
  change Measure.map openSet
    (FKLimit.bernoulliProduct (fun _ : BBR.Site 2 => s) : Measure _) = BBR.sitePerc 2 s
  rw [FK.EssentialWindow.map_openSet_bernoulliProduct,
    PercLib.Probability.prodBernoulli_const]
  rfl

lemma theta0_zero (d : ℕ) : BBR.theta0 d 0 = 0 := by
  have hno : ¬ BBR.OriginInInfiniteCluster (∅ : Set (BBR.Site d)) := by
    intro h
    obtain ⟨x, hx⟩ := h.nonempty
    exact hx.mem_right
  simp [BBR.theta0, BBR.sitePerc, hno]

/-- BBR's Peierls bound gives a strictly sub-one activation parameter whose
ordinary coarse site cluster is infinite with nonzero probability. -/
theorem exists_interior_sitePercolating_rate :
    ∃ s : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ BBR.theta0 2 s ≠ 0 := by
  have hex : ∃ s : unitInterval, (s : ℝ) < 1 ∧ BBR.theta0 2 s ≠ 0 := by
    by_contra hn
    push Not at hn
    by_cases h1 : BBR.theta0 2 1 = 0
    · have hset : {x : ℝ | ∃ p : unitInterval, (p : ℝ) = x ∧ BBR.theta0 2 p = 0} =
          Set.Icc 0 1 := by
        ext x
        constructor
        · rintro ⟨p, rfl, hp⟩
          exact ⟨p.2.1, p.2.2⟩
        · intro hx
          let p : unitInterval := ⟨x, hx.1, hx.2⟩
          refine ⟨p, rfl, ?_⟩
          rcases lt_or_eq_of_le hx.2 with hlt | heq
          · exact hn p hlt
          · have hp : p = 1 := Subtype.ext heq
            rw [hp]
            exact h1
      have hpc : BBR.pcSite 2 = 1 := by
        unfold BBR.pcSite
        rw [hset]
        exact csSup_Icc (by norm_num)
      have hlt := BBR.pcSite_lt_one (d := 2) (by norm_num)
      rw [hpc] at hlt
      exact (lt_irrefl 1 hlt)
    · have hset : {x : ℝ | ∃ p : unitInterval, (p : ℝ) = x ∧ BBR.theta0 2 p = 0} =
          Set.Ico 0 1 := by
        ext x
        constructor
        · rintro ⟨p, rfl, hp⟩
          refine ⟨p.2.1, lt_of_le_of_ne p.2.2 ?_⟩
          intro heq
          apply h1
          have hp1 : p = 1 := Subtype.ext heq
          rw [← hp1]
          exact hp
        · intro hx
          let p : unitInterval := ⟨x, hx.1, hx.2.le⟩
          exact ⟨p, rfl, hn p hx.2⟩
      have hpc : BBR.pcSite 2 = 1 := by
        unfold BBR.pcSite
        rw [hset]
        exact csSup_Ico (by norm_num)
      have hlt := BBR.pcSite_lt_one (d := 2) (by norm_num)
      rw [hpc] at hlt
      exact (lt_irrefl 1 hlt)
  obtain ⟨s, hs1, hs⟩ := hex
  refine ⟨s, ?_, hs1, hs⟩
  by_contra hs0
  have heq : s = 0 := Subtype.ext (le_antisymm (le_of_not_gt hs0) s.2.1)
  subst s
  exact hs (theta0_zero 2)

/-- Positive coarse percolation forces positive enhanced root percolation at
*every* ordinary bond parameter, by the deterministic coarse-path comparison. -/
theorem enhancedRootEvent_ne_zero (p s : unitInterval) (hs : BBR.theta0 2 s ≠ 0) :
    (starLaw p s) EnhancedRootEvent ≠ 0 := by
  have hpre : (starLaw p s)
      (coarseActive ⁻¹' {A : Set (BBR.Site 2) | BBR.OriginInInfiniteCluster A}) ≠ 0 := by
    rw [← Measure.map_apply measurable_coarseActive measurableSet_originInfinite,
      map_coarseActive_starLaw]
    intro hzero
    apply hs
    unfold BBR.theta0
    rw [hzero]
    rfl
  intro hevent
  apply hpre
  apply measure_mono_null (μ := starLaw p s) ?_ hevent
  intro χ hχ
  exact root_of_coarse_infinite χ hχ

theorem enhancedRootEvent_pos (p s : unitInterval) (hs : BBR.theta0 2 s ≠ 0) :
    0 < (starLaw p s) EnhancedRootEvent :=
  (pos_iff_ne_zero).2 (enhancedRootEvent_ne_zero p s hs)

/-- The scoped strict comparison: the explicit positive ordinary rate `1/8`
has zero percolation, while an interior independent star rate has positive
enhanced root percolation under the actual joint product law. -/
theorem exists_interior_activation_strict_comparison :
    ∃ s : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧
      percolationProb gridGraph origin baseRate = 0 ∧
      0 < (starLaw baseRate s) EnhancedRootEvent := by
  obtain ⟨s, hs0, hs1, hs⟩ := exists_interior_sitePercolating_rate
  exact ⟨s, hs0, hs1, base_nonpercolating, enhancedRootEvent_pos baseRate s hs⟩

end

end FK.SquareLatticeStar
