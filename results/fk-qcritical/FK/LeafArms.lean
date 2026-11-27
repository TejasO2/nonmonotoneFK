import FK.LeafWalk
import FK.BurtonKeaneWeak

/-!
# Three-way arms from central attachment paths

Transport three central junction branches to a receiving graph and splice them
to separated exterior arms.  Contacts at other attachment vertices are handled
explicitly: external walks necessarily contain their own starting attachment,
so a blanket exclusion of every central vertex would be inconsistent.
-/

open scoped Classical
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane

universe u v

variable {B : Type u} (H : SimpleGraph B) (attach : Fin 3 → B)
variable {V : Type v} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- **Three-way arms from central attachment paths.**  The exterior witnesses
may be chosen at every scale, as when they are supplied by infinite exterior
components.  Other-parent contacts need no separate incidence axiom: pairwise
separation of the central branches proves that such a contact is the centre. -/
theorem threeWayArms_of_leaf_attachments [DecidableEq V]
    {T : SimpleGraph (B ⊕ Fin 3)} (hle : T ≤ withLeaves H attach)
    (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hFinj : Function.Injective (F ∘ Sum.inl))
    (hFopen : ∀ a b (hab : H.Adj a b),
      ω ⟨s(F (.inl a), F (.inl b)), hFadj a b hab⟩ = true)
    {y : B} (pa : T.Walk (.inl y) (.inr 0)) (pb : T.Walk (.inl y) (.inr 1))
    (pc : T.Walk (.inl y) (.inr 2))
    (hpa : pa.IsPath) (hpb : pb.IsPath) (hpc : pc.IsPath)
    (hab : ∀ z ∈ pa.support, z ∈ pb.support → z = .inl y)
    (hac : ∀ z ∈ pa.support, z ∈ pc.support → z = .inl y)
    (hbc : ∀ z ∈ pb.support, z ∈ pc.support → z = .inl y)
    (h1A : .inr 1 ∉ pa.support) (h2A : .inr 2 ∉ pa.support)
    (h0B : .inr 0 ∉ pb.support) (h2B : .inr 2 ∉ pb.support)
    (h0C : .inr 0 ∉ pc.support) (h1C : .inr 1 ∉ pc.support)
    (z0 z1 z2 : ℕ → V)
    (qa : ∀ n, G.Walk (F (.inl (attach 0))) (z0 n))
    (qb : ∀ n, G.Walk (F (.inl (attach 1))) (z1 n))
    (qc : ∀ n, G.Walk (F (.inl (attach 2))) (z2 n))
    (hqa : ∀ n, IsOpenIn ω Set.univ (qa n))
    (hqb : ∀ n, IsOpenIn ω Set.univ (qb n))
    (hqc : ∀ n, IsOpenIn ω Set.univ (qc n))
    (hQ01 : ∀ n z, z ∈ (qa n).support → z ∈ (qb n).support → z = F (.inl y))
    (hQ02 : ∀ n z, z ∈ (qa n).support → z ∈ (qc n).support → z = F (.inl y))
    (hQ12 : ∀ n z, z ∈ (qb n).support → z ∈ (qc n).support → z = F (.inl y))
    (hC01 : ∀ n a z, F (.inl a) = z → z ∈ (qb n).support → a ≠ attach 1 → False)
    (hC02 : ∀ n a z, F (.inl a) = z → z ∈ (qc n).support → a ≠ attach 2 → False)
    (hC10 : ∀ n a z, F (.inl a) = z → z ∈ (qa n).support → a ≠ attach 0 → False)
    (hC12 : ∀ n a z, F (.inl a) = z → z ∈ (qc n).support → a ≠ attach 2 → False)
    (hC20 : ∀ n a z, F (.inl a) = z → z ∈ (qa n).support → a ≠ attach 0 → False)
    (hC21 : ∀ n a z, F (.inl a) = z → z ∈ (qb n).support → a ≠ attach 1 → False)
    (hn0 : ∀ n, n ≤ G.dist (F (.inl y)) (z0 n))
    (hn1 : ∀ n, n ≤ G.dist (F (.inl y)) (z1 n))
    (hn2 : ∀ n, n ≤ G.dist (F (.inl y)) (z2 n)) :
    ∀ n : ℕ, ThreeWayArms G ω (F (.inl y)) n := by
  obtain ⟨ca, hca, hcaSub, hcaNo⟩ := exists_stripLeaf H attach hle pa hpa (by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact h1A
    · exact h2A)
  obtain ⟨cb, hcb, hcbSub, hcbNo⟩ := exists_stripLeaf H attach hle pb hpb (by
    intro j hj
    fin_cases j
    · exact h0B
    · exact (hj rfl).elim
    · exact h2B)
  obtain ⟨cc, hcc, hccSub, hccNo⟩ := exists_stripLeaf H attach hle pc hpc (by
    intro j hj
    fin_cases j
    · exact h0C
    · exact h1C
    · exact (hj rfl).elim)
  let Ra := mappedCentralWalk H attach F hFadj hle ca hcaNo
  let Rb := mappedCentralWalk H attach F hFadj hle cb hcbNo
  let Rc := mappedCentralWalk H attach F hFadj hle cc hccNo
  have hRa : Ra.IsPath := isPath_mappedCentralWalk H attach F hFadj hFinj hle ca hca hcaNo
  have hRb : Rb.IsPath := isPath_mappedCentralWalk H attach F hFadj hFinj hle cb hcb hcbNo
  have hRc : Rc.IsPath := isPath_mappedCentralWalk H attach F hFadj hFinj hle cc hcc hccNo
  have hRaOpen : IsOpenIn ω Set.univ Ra :=
    isOpenIn_mappedCentralWalk H attach F hFadj hFopen hle ca hcaNo
  have hRbOpen : IsOpenIn ω Set.univ Rb :=
    isOpenIn_mappedCentralWalk H attach F hFadj hFopen hle cb hcbNo
  have hRcOpen : IsOpenIn ω Set.univ Rc :=
    isOpenIn_mappedCentralWalk H attach F hFadj hFopen hle cc hccNo
  have hAB : ∀ z ∈ Ra.support, z ∈ Rb.support → z = F (.inl y) :=
    mappedCentral_meet H attach F hFadj hFinj hle ca cb hcaNo hcbNo
      (fun z hzA hzB => hab z (hcaSub hzA) (hcbSub hzB))
  have hAC : ∀ z ∈ Ra.support, z ∈ Rc.support → z = F (.inl y) :=
    mappedCentral_meet H attach F hFadj hFinj hle ca cc hcaNo hccNo
      (fun z hzA hzC => hac z (hcaSub hzA) (hccSub hzC))
  have hBC : ∀ z ∈ Rb.support, z ∈ Rc.support → z = F (.inl y) :=
    mappedCentral_meet H attach F hFadj hFinj hle cb cc hcbNo hccNo
      (fun z hzB hzC => hbc z (hcbSub hzB) (hccSub hzC))
  refine fun n => Weak.threeWayArms_splice_weak (G := G) (ω := ω) (F (.inl y)) n
    Ra Rb Rc (qa n) (qb n) (qc n) hRaOpen hRbOpen hRcOpen
    (hqa n) (hqb n) (hqc n) hAB hAC hBC ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hn0 n) (hn1 n) (hn2 n)
  · exact mappedCentral_disjoint_except_center H attach F hFadj hle ca hcaNo (attach 1)
      (fun h => Sum.inl.inj (hab (.inl (attach 1)) (hcaSub h) (hcbSub cb.end_mem_support)))
      {z | z ∈ (qb n).support} (fun a ha hza => hC01 n a (F (.inl a)) rfl hza ha)
  · exact mappedCentral_disjoint_except_center H attach F hFadj hle ca hcaNo (attach 2)
      (fun h => Sum.inl.inj (hac (.inl (attach 2)) (hcaSub h) (hccSub cc.end_mem_support)))
      {z | z ∈ (qc n).support} (fun a ha hza => hC02 n a (F (.inl a)) rfl hza ha)
  · exact mappedCentral_disjoint_except_center H attach F hFadj hle cb hcbNo (attach 0)
      (fun h => Sum.inl.inj (hab (.inl (attach 0)) (hcaSub ca.end_mem_support) (hcbSub h)))
      {z | z ∈ (qa n).support} (fun a ha hza => hC10 n a (F (.inl a)) rfl hza ha)
  · exact mappedCentral_disjoint_except_center H attach F hFadj hle cb hcbNo (attach 2)
      (fun h => Sum.inl.inj (hbc (.inl (attach 2)) (hcbSub h) (hccSub cc.end_mem_support)))
      {z | z ∈ (qc n).support} (fun a ha hza => hC12 n a (F (.inl a)) rfl hza ha)
  · exact mappedCentral_disjoint_except_center H attach F hFadj hle cc hccNo (attach 0)
      (fun h => Sum.inl.inj (hac (.inl (attach 0)) (hcaSub ca.end_mem_support) (hccSub h)))
      {z | z ∈ (qa n).support} (fun a ha hza => hC20 n a (F (.inl a)) rfl hza ha)
  · exact mappedCentral_disjoint_except_center H attach F hFadj hle cc hccNo (attach 1)
      (fun h => Sum.inl.inj (hbc (.inl (attach 1)) (hcbSub cb.end_mem_support) (hccSub h)))
      {z | z ∈ (qb n).support} (fun a ha hza => hC21 n a (F (.inl a)) rfl hza ha)
  · exact hQ01 n
  · exact hQ02 n
  · exact hQ12 n
