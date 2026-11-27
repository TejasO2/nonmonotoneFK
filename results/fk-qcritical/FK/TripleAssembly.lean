import FK.ConnectedSupport
import FK.LeafArms

/-!
# Deterministic assembly of three arms

Three distinct infinite open clusters are joined by opening only the edges
internal to one finite connected set.  The three exterior pieces are chosen in
components avoiding all edges incident to that set, so their separation is
preserved by the finite patch.
-/

open scoped Classical
open CurvatureVariance.Infra.Percolation
open Set

namespace FK.BurtonKeane

universe u
variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

namespace AssemblyBranch

variable {U : Set V}

/-- An endpoint at prescribed distance in the infinite avoided component. -/
noncomputable def farEndpoint [G.LocallyFinite] (hG : G.Connected)
    (B : AssemblyBranch G ω U) (y : V) (n : ℕ) : V :=
  Classical.choose (exists_far_mem_of_infinite hG B.stemInf y n)

lemma farEndpoint_dist [G.LocallyFinite] (hG : G.Connected)
    (B : AssemblyBranch G ω U) (y : V) (n : ℕ) :
    n ≤ G.dist y (B.farEndpoint hG y n) :=
  (Classical.choose_spec (exists_far_mem_of_infinite hG B.stemInf y n)).1

/-- A chosen avoided open arm to `farEndpoint`. -/
noncomputable def farArm [G.LocallyFinite] (hG : G.Connected)
    (B : AssemblyBranch G ω U) (y : V) (n : ℕ) :
    G.Walk B.stem (B.farEndpoint hG y n) :=
  Classical.choose (Classical.choose_spec
    (exists_far_mem_of_infinite hG B.stemInf y n)).2

lemma farArm_open [G.LocallyFinite] (hG : G.Connected)
    (B : AssemblyBranch G ω U) (y : V) (n : ℕ) :
    IsOpenIn ω (Set.univ \ incidence G U) (B.farArm hG y n) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_far_mem_of_infinite hG B.stemInf y n)).2

/-- The attachment edge followed by the chosen arm is open after the patch. -/
lemma farWalk_open [G.LocallyFinite] (hG : G.Connected)
    (B : AssemblyBranch G ω U) (y : V) (n : ℕ) :
    IsOpenIn (openInternal U ω) Set.univ (B.walk (B.farArm hG y n)) := by
  apply walk_open
  apply isOpenIn_cons.mpr
  exact ⟨⟨Set.mem_univ _, B.adj_open⟩,
    (B.farArm_open hG y n).mono_edges (Set.subset_univ _)⟩

lemma avoiding_nonConnected_stems_of_original {B B' : AssemblyBranch G ω U}
    (h : ¬ OpenConnected G ω Set.univ B.original B'.original) :
    ¬ OpenConnected G ω (Set.univ \ incidence G U) B.stem B'.stem := by
  apply avoiding_nonConnected_stems
  apply avoiding_nonConnected
  intro hconn
  obtain ⟨q, hq⟩ := hconn
  apply h
  exact ⟨q.append B'.link.reverse, isOpenIn_append.mpr
    ⟨hq.mono_edges (Set.subset_univ _),
      (isOpenIn_reverse B'.link B'.link_open).mono_edges (Set.subset_univ _)⟩⟩

/-- An outside vertex on an attachment walk already lies on its avoided arm. -/
lemma mem_arm_of_not_mem {B : AssemblyBranch G ω U} {w : V}
    {arm : G.Walk B.stem w} {x : V}
    (hx : x ∈ (B.walk arm).support) (hxU : x ∉ U) : x ∈ arm.support := by
  simp only [walk, SimpleGraph.Walk.support_cons, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact (hxU B.parent_mem).elim
  · exact hx

/-- A central-image vertex on an attachment walk is its selected parent. -/
lemma eq_parent_of_central_mem_walk {B : AssemblyBranch G ω U} {w : V}
    {arm : G.Walk B.stem w} (harm : IsOpenIn ω (Set.univ \ incidence G U) arm)
    {a : U} {x : V} (hax : (a : V) = x) (hx : x ∈ (B.walk arm).support) :
    (a : V) = B.parent := by
  have hxU : x ∈ U := hax ▸ a.property
  exact hax.trans (walk_central_eq_parent harm hx hxU)

/-- Two distinct exterior attachment walks meet only where their equal
parents are certified to be the junction centre. -/
lemma eq_center_of_mem_walk_mem_walk {B B' : AssemblyBranch G ω U} {w w' : V}
    {arm : G.Walk B.stem w} {arm' : G.Walk B'.stem w'}
    (harm : IsOpenIn ω (Set.univ \ incidence G U) arm)
    (harm' : IsOpenIn ω (Set.univ \ incidence G U) arm')
    (hnon : ¬ OpenConnected G ω (Set.univ \ incidence G U) B.stem B'.stem)
    {y : V} (hparents : B.parent = B'.parent → B.parent = y)
    {x : V} (hx : x ∈ (B.walk arm).support) (hx' : x ∈ (B'.walk arm').support) :
    x = y := by
  rcases walk_parent_or_not_mem harm hx with hxp | hxU
  · rcases walk_parent_or_not_mem harm' hx' with hxp' | hxU'
    · rw [hxp, hparents (hxp.symm.trans hxp')]
    · exact (hxU' (hxp.symm ▸ B.parent_mem)).elim
  · rcases walk_parent_or_not_mem harm' hx' with hxp' | hxU'
    · exact (hxU (hxp'.symm ▸ B'.parent_mem)).elim
    · exact (disjoint_support_of_not_openConnected arm arm' harm harm' hnon x
        (mem_arm_of_not_mem hx hxU) (mem_arm_of_not_mem hx' hxU')).elim

end AssemblyBranch

/-- **Deterministic three-cluster encounter.**  If three prescribed vertices
lie in pairwise distinct infinite open clusters, then there is a finite set
`U` and a centre having three disjoint open arms at every scale after only the
edges internal to `U` are opened. -/
theorem exists_threeWayArms_openInternal_of_three_infinite [G.LocallyFinite]
    (hG : G.Connected) {r₀ r₁ r₂ : V}
    (hinf₀ : {z | OpenConnected G ω Set.univ r₀ z}.Infinite)
    (hinf₁ : {z | OpenConnected G ω Set.univ r₁ z}.Infinite)
    (hinf₂ : {z | OpenConnected G ω Set.univ r₂ z}.Infinite)
    (h₀₁ : ¬ OpenConnected G ω Set.univ r₀ r₁)
    (h₀₂ : ¬ OpenConnected G ω Set.univ r₀ r₂)
    (h₁₂ : ¬ OpenConnected G ω Set.univ r₁ r₂) :
    ∃ U : Set V, U.Finite ∧ ∃ y : V,
      ∀ n : ℕ, ThreeWayArms G (openInternal U ω) y n := by
  obtain ⟨U, hU, hr₀, hr₁, hr₂, hUconn⟩ := exists_connected_support hG r₀ r₁ r₂
  obtain ⟨B₀, hB₀⟩ := AssemblyBranch.exists_at_original hG hU hr₀ hinf₀
  obtain ⟨B₁, hB₁⟩ := AssemblyBranch.exists_at_original hG hU hr₁ hinf₁
  obtain ⟨B₂, hB₂⟩ := AssemblyBranch.exists_at_original hG hU hr₂ hinf₂
  have hn₀₁ : ¬ OpenConnected G ω (Set.univ \ incidence G U) B₀.stem B₁.stem := by
    apply AssemblyBranch.avoiding_nonConnected_stems_of_original
    simpa only [hB₀, hB₁] using h₀₁
  have hn₀₂ : ¬ OpenConnected G ω (Set.univ \ incidence G U) B₀.stem B₂.stem := by
    apply AssemblyBranch.avoiding_nonConnected_stems_of_original
    simpa only [hB₀, hB₂] using h₀₂
  have hn₁₂ : ¬ OpenConnected G ω (Set.univ \ incidence G U) B₁.stem B₂.stem := by
    apply AssemblyBranch.avoiding_nonConnected_stems_of_original
    simpa only [hB₁, hB₂] using h₁₂
  let H : SimpleGraph U := G.induce U
  let attach : Fin 3 → U := ![
    ⟨B₀.parent, B₀.parent_mem⟩, ⟨B₁.parent, B₁.parent_mem⟩,
    ⟨B₂.parent, B₂.parent_mem⟩]
  let F : U ⊕ Fin 3 → V
    | .inl a => a.1
    | .inr _ => r₀
  have hFadj : ∀ a b : U, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)) := by
    intro a b hab
    exact hab
  have hFinj : Function.Injective (F ∘ Sum.inl) := by
    intro a b hab
    apply Subtype.ext
    exact hab
  have hFopen : ∀ a b (hab : H.Adj a b),
      openInternal U ω ⟨s(F (.inl a), F (.inl b)), hFadj a b hab⟩ = true := by
    intro a b hab
    apply openInternal_of_mem
    refine ⟨hFadj a b hab, ?_⟩
    intro x hx
    have hx' : x = F (.inl a) ∨ x = F (.inl b) := by simpa using hx
    rcases hx' with rfl | rfl
    · exact a.property
    · exact b.property
  obtain ⟨T, hle, hT, y, pa, pb, pc, hpa, hpb, hpc, hab, hac, hbc,
    h1A, h2A, h0B, h2B, h0C, h1C⟩ :=
      exists_central_three_way_junction H attach hUconn
  obtain ⟨ca, _, hcaSub, _⟩ := exists_stripLeaf H attach hle pa hpa (by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact h1A
    · exact h2A)
  obtain ⟨cb, _, hcbSub, _⟩ := exists_stripLeaf H attach hle pb hpb (by
    intro j hj
    fin_cases j
    · exact h0B
    · exact (hj rfl).elim
    · exact h2B)
  obtain ⟨cc, _, hccSub, _⟩ := exists_stripLeaf H attach hle pc hpc (by
    intro j hj
    fin_cases j
    · exact h0C
    · exact h1C
    · exact (hj rfl).elim)
  have hmem₀ : Sum.inl (attach 0) ∈ pa.support := hcaSub ca.end_mem_support
  have hmem₁ : Sum.inl (attach 1) ∈ pb.support := hcbSub cb.end_mem_support
  have hmem₂ : Sum.inl (attach 2) ∈ pc.support := hccSub cc.end_mem_support
  have hparents₀₁ : B₀.parent = B₁.parent → B₀.parent = F (.inl y) := by
    intro hp
    have heq : attach 0 = attach 1 := by
      apply Subtype.ext
      simpa [attach] using hp
    have hy : attach 0 = y := by
      apply Sum.inl.inj
      apply hab (.inl (attach 0)) hmem₀
      rw [heq]
      exact hmem₁
    have hy' := congrArg (fun a : U => (a : V)) hy
    simpa [attach, F] using hy'
  have hparents₀₂ : B₀.parent = B₂.parent → B₀.parent = F (.inl y) := by
    intro hp
    have heq : attach 0 = attach 2 := by
      apply Subtype.ext
      simpa [attach] using hp
    have hy : attach 0 = y := by
      apply Sum.inl.inj
      apply hac (.inl (attach 0)) hmem₀
      rw [heq]
      exact hmem₂
    have hy' := congrArg (fun a : U => (a : V)) hy
    simpa [attach, F] using hy'
  have hparents₁₂ : B₁.parent = B₂.parent → B₁.parent = F (.inl y) := by
    intro hp
    have heq : attach 1 = attach 2 := by
      apply Subtype.ext
      simpa [attach] using hp
    have hy : attach 1 = y := by
      apply Sum.inl.inj
      apply hbc (.inl (attach 1)) hmem₁
      rw [heq]
      exact hmem₂
    have hy' := congrArg (fun a : U => (a : V)) hy
    simpa [attach, F] using hy'
  let z₀ : ℕ → V := fun n => B₀.farEndpoint hG (F (.inl y)) n
  let z₁ : ℕ → V := fun n => B₁.farEndpoint hG (F (.inl y)) n
  let z₂ : ℕ → V := fun n => B₂.farEndpoint hG (F (.inl y)) n
  let qa : ∀ n, G.Walk (F (.inl (attach 0))) (z₀ n) := fun n => by
    change G.Walk B₀.parent (B₀.farEndpoint hG (F (.inl y)) n)
    exact B₀.walk (B₀.farArm hG (F (.inl y)) n)
  let qb : ∀ n, G.Walk (F (.inl (attach 1))) (z₁ n) := fun n => by
    change G.Walk B₁.parent (B₁.farEndpoint hG (F (.inl y)) n)
    exact B₁.walk (B₁.farArm hG (F (.inl y)) n)
  let qc : ∀ n, G.Walk (F (.inl (attach 2))) (z₂ n) := fun n => by
    change G.Walk B₂.parent (B₂.farEndpoint hG (F (.inl y)) n)
    exact B₂.walk (B₂.farArm hG (F (.inl y)) n)
  have hqa : ∀ n, IsOpenIn (openInternal U ω) Set.univ (qa n) := by
    intro n
    exact B₀.farWalk_open hG (F (.inl y)) n
  have hqb : ∀ n, IsOpenIn (openInternal U ω) Set.univ (qb n) := by
    intro n
    exact B₁.farWalk_open hG (F (.inl y)) n
  have hqc : ∀ n, IsOpenIn (openInternal U ω) Set.univ (qc n) := by
    intro n
    exact B₂.farWalk_open hG (F (.inl y)) n
  refine ⟨U, hU, F (.inl y), ?_⟩
  apply threeWayArms_of_leaf_attachments H attach hle F hFadj hFinj hFopen
    pa pb pc hpa hpb hpc hab hac hbc h1A h2A h0B h2B h0C h1C
    z₀ z₁ z₂ qa qb qc hqa hqb hqc
  · intro n z hz₀ hz₁
    change z ∈ (B₀.walk (B₀.farArm hG (F (.inl y)) n)).support at hz₀
    change z ∈ (B₁.walk (B₁.farArm hG (F (.inl y)) n)).support at hz₁
    exact AssemblyBranch.eq_center_of_mem_walk_mem_walk
      (B₀.farArm_open hG (F (.inl y)) n) (B₁.farArm_open hG (F (.inl y)) n)
      hn₀₁ hparents₀₁ hz₀ hz₁
  · intro n z hz₀ hz₂
    change z ∈ (B₀.walk (B₀.farArm hG (F (.inl y)) n)).support at hz₀
    change z ∈ (B₂.walk (B₂.farArm hG (F (.inl y)) n)).support at hz₂
    exact AssemblyBranch.eq_center_of_mem_walk_mem_walk
      (B₀.farArm_open hG (F (.inl y)) n) (B₂.farArm_open hG (F (.inl y)) n)
      hn₀₂ hparents₀₂ hz₀ hz₂
  · intro n z hz₁ hz₂
    change z ∈ (B₁.walk (B₁.farArm hG (F (.inl y)) n)).support at hz₁
    change z ∈ (B₂.walk (B₂.farArm hG (F (.inl y)) n)).support at hz₂
    exact AssemblyBranch.eq_center_of_mem_walk_mem_walk
      (B₁.farArm_open hG (F (.inl y)) n) (B₂.farArm_open hG (F (.inl y)) n)
      hn₁₂ hparents₁₂ hz₁ hz₂
  · intro n b z hF hz hne
    apply hne
    apply Subtype.ext
    change z ∈ (B₁.walk (B₁.farArm hG (F (.inl y)) n)).support at hz
    have hp := AssemblyBranch.eq_parent_of_central_mem_walk
      (B := B₁) (B₁.farArm_open hG (F (.inl y)) n)
      (by simpa only [F] using hF) hz
    simpa [attach] using hp
  · intro n b z hF hz hne
    apply hne
    apply Subtype.ext
    change z ∈ (B₂.walk (B₂.farArm hG (F (.inl y)) n)).support at hz
    have hp := AssemblyBranch.eq_parent_of_central_mem_walk
      (B := B₂) (B₂.farArm_open hG (F (.inl y)) n)
      (by simpa only [F] using hF) hz
    simpa [attach] using hp
  · intro n b z hF hz hne
    apply hne
    apply Subtype.ext
    change z ∈ (B₀.walk (B₀.farArm hG (F (.inl y)) n)).support at hz
    have hp := AssemblyBranch.eq_parent_of_central_mem_walk
      (B := B₀) (B₀.farArm_open hG (F (.inl y)) n)
      (by simpa only [F] using hF) hz
    simpa [attach] using hp
  · intro n b z hF hz hne
    apply hne
    apply Subtype.ext
    change z ∈ (B₂.walk (B₂.farArm hG (F (.inl y)) n)).support at hz
    have hp := AssemblyBranch.eq_parent_of_central_mem_walk
      (B := B₂) (B₂.farArm_open hG (F (.inl y)) n)
      (by simpa only [F] using hF) hz
    simpa [attach] using hp
  · intro n b z hF hz hne
    apply hne
    apply Subtype.ext
    change z ∈ (B₀.walk (B₀.farArm hG (F (.inl y)) n)).support at hz
    have hp := AssemblyBranch.eq_parent_of_central_mem_walk
      (B := B₀) (B₀.farArm_open hG (F (.inl y)) n)
      (by simpa only [F] using hF) hz
    simpa [attach] using hp
  · intro n b z hF hz hne
    apply hne
    apply Subtype.ext
    change z ∈ (B₁.walk (B₁.farArm hG (F (.inl y)) n)).support at hz
    have hp := AssemblyBranch.eq_parent_of_central_mem_walk
      (B := B₁) (B₁.farArm_open hG (F (.inl y)) n)
      (by simpa only [F] using hF) hz
    simpa [attach] using hp
  · intro n
    exact B₀.farEndpoint_dist hG (F (.inl y)) n
  · intro n
    exact B₁.farEndpoint_dist hG (F (.inl y)) n
  · intro n
    exact B₂.farEndpoint_dist hG (F (.inl y)) n


end FK.BurtonKeane
