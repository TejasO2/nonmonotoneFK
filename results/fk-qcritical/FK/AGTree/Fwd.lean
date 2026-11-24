import FK.AGTree.Edges

/-!
# Forward clusters of the two-class tree and the branching recursion
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

/-! ### Prefixes -/

/-- `Pref l₁ l₂`: `l₁` is a prefix of `l₂`. -/
def Pref (l₁ l₂ : List A) : Prop := ∃ t : List A, l₂ = l₁ ++ t

lemma Pref.refl (l : List A) : Pref l l := ⟨[], (List.append_nil l).symm⟩

lemma Pref.trans {a b c : List A} (h1 : Pref a b) (h2 : Pref b c) : Pref a c := by
  obtain ⟨t1, rfl⟩ := h1
  obtain ⟨t2, rfl⟩ := h2
  exact ⟨t1 ++ t2, List.append_assoc _ _ _⟩

lemma Pref.snoc (u : V) (a : A) (h : u.Valid a) : Pref u.w (u.snoc a h).w := ⟨[a], rfl⟩

lemma Pref.eq_of_len {l₁ l₂ v : List A} (h1 : Pref l₁ v) (h2 : Pref l₂ v)
    (hlen : l₁.length = l₂.length) : l₁ = l₂ := by
  obtain ⟨t1, h1⟩ := h1
  obtain ⟨t2, h2⟩ := h2
  have h : l₁ ++ t1 = l₂ ++ t2 := h1.symm.trans h2
  exact (List.append_inj h hlen).1

/-! ### The forward cluster -/

/-- The child edges along the letters of `l`, starting at `u`, are all open. -/
def ChainOpen (ω : G.edgeSet → Bool) (u : V) : List A → Prop
  | [] => True
  | a :: rest => ∃ (h : u.Valid a), ω (childE (⟨(u, a), h⟩ : Echild)) = true ∧
      ChainOpen ω (u.snoc a h) rest

/-- The forward cluster of `u` contains a vertex at distance `n` below `u`. -/
def Fwd (ω : G.edgeSet → Bool) (u : V) (n : ℕ) : Prop :=
  ∃ l : List A, l.length = n ∧ ChainOpen ω u l

lemma fwd_zero (ω : G.edgeSet → Bool) (u : V) : Fwd ω u 0 := ⟨[], rfl, trivial⟩

lemma fwd_succ (ω : G.edgeSet → Bool) (u : V) (n : ℕ) :
    Fwd ω u (n + 1) ↔ ∃ (a : A) (h : u.Valid a),
      ω (childE (⟨(u, a), h⟩ : Echild)) = true ∧ Fwd ω (u.snoc a h) n := by
  constructor
  · rintro ⟨l, hlen, hc⟩
    cases l with
    | nil => simp at hlen
    | cons a rest =>
      obtain ⟨h, hω, hrest⟩ := hc
      exact ⟨a, h, hω, rest, by simpa using hlen, hrest⟩
  · rintro ⟨a, h, hω, l, hlen, hcl⟩
    exact ⟨a :: l, by simp [hlen], h, hω, hcl⟩

/-- The child edges lying in the forward subtree of `u`. -/
def subE (u : V) : Set G.edgeSet :=
  {e | ∃ (v : V) (a : A) (h : v.Valid a), e = childE (⟨(v, a), h⟩ : Echild) ∧ Pref u.w v.w}

lemma subE_mono {u v : V} (hv : Pref u.w v.w) : subE v ⊆ subE u :=
  fun _ ⟨w, a, h, he, hp⟩ => ⟨w, a, h, he, hv.trans hp⟩

lemma childE_mem_subE {u : V} (hu : Pref u.w u.w) {a : A} (h : u.Valid a) :
    childE (⟨(u, a), h⟩ : Echild) ∈ subE u :=
  ⟨u, a, h, rfl, hu⟩

lemma childE_notMem_subE_snoc {u : V} {a : A} (h : u.Valid a) :
    childE (⟨(u, a), h⟩ : Echild) ∉ subE (u.snoc a h) := by
  rintro ⟨v, b, hb, he, hp⟩
  have h1 : (⟨(v, b), hb⟩ : Echild) = ⟨(u, a), h⟩ := childE_inj he.symm
  have hv : v = u := by simpa using congrArg (fun x : Echild => x.1.1) h1
  rw [hv] at hp
  obtain ⟨t, ht⟩ := hp
  have hlen : u.w.length = (u.snoc a h).w.length + t.length := by
    rw [ht]; simp only [V.snoc_w, List.length_append, List.length_singleton]
  simp only [V.snoc_w, List.length_append, List.length_singleton] at hlen
  omega

lemma childE_notMem_subE_snoc_of_ne {u : V} {a b : A} (hab : a ≠ b)
    (ha : u.Valid a) (hb : u.Valid b) :
    childE (⟨(u, a), ha⟩ : Echild) ∉ subE (u.snoc b hb) := by
  rintro ⟨v, c, hc, he, hp⟩
  have h1 : (⟨(v, c), hc⟩ : Echild) = ⟨(u, a), ha⟩ := childE_inj he.symm
  have hv : v = u := by simpa using congrArg (fun x : Echild => x.1.1) h1
  rw [hv] at hp
  obtain ⟨t, ht⟩ := hp
  have hlen : u.w.length = (u.snoc b hb).w.length + t.length := by
    rw [ht]; simp only [V.snoc_w, List.length_append, List.length_singleton]
  simp only [V.snoc_w, List.length_append, List.length_singleton] at hlen
  omega

lemma subE_snoc_disjoint {u : V} {a b : A} (hab : a ≠ b) (ha : u.Valid a) (hb : u.Valid b) :
    Disjoint (subE (u.snoc a ha)) (subE (u.snoc b hb)) := by
  refine Set.disjoint_left.2 ?_
  rintro e ⟨v, c, hc, he, hp1⟩ ⟨v', c', hc', he', hp2⟩
  rw [he] at he'
  have h1 := childE_inj he'
  have hvv : v = v' := by simpa using congrArg (fun x : Echild => x.1.1) h1
  subst hvv
  have hlen : (u.snoc a ha).w.length = (u.snoc b hb).w.length := by simp
  have heq : (u.snoc a ha).w = (u.snoc b hb).w := Pref.eq_of_len hp1 hp2 hlen
  simp only [V.snoc_w] at heq
  have : [a] = [b] := List.append_cancel_left heq
  exact hab (by simpa using this)

/-! ### Dependence on coordinate blocks -/

lemma DependsOn.univ {ι : Type*} (D : Set ι) : DependsOn (Set.univ : Set (ι → Bool)) D :=
  fun _ _ _ => Iff.rfl

lemma DependsOn.inter {ι : Type*} {A B : Set (ι → Bool)} {D : Set ι}
    (h1 : DependsOn A D) (h2 : DependsOn B D) : DependsOn (A ∩ B) D :=
  fun ω η h => by simp only [Set.mem_inter_iff]; rw [h1 ω η h, h2 ω η h]

lemma DependsOn.compl {ι : Type*} {A : Set (ι → Bool)} {D : Set ι}
    (h : DependsOn A D) : DependsOn Aᶜ D :=
  fun ω η h' => by simp only [Set.mem_compl_iff]; rw [h ω η h']

lemma DependsOn.union {ι : Type*} {A B : Set (ι → Bool)} {D : Set ι}
    (h1 : DependsOn A D) (h2 : DependsOn B D) : DependsOn (A ∪ B) D :=
  fun ω η h => by simp only [Set.mem_union]; rw [h1 ω η h, h2 ω η h]

lemma DependsOn.iUnion {ι κ : Type*} {A : κ → Set (ι → Bool)} {D : Set ι}
    (h : ∀ k, DependsOn (A k) D) : DependsOn (⋃ k, A k) D :=
  fun ω η h' => by simp only [Set.mem_iUnion]; exact exists_congr (fun k => h k ω η h')

lemma DependsOn.mono {ι : Type*} {A : Set (ι → Bool)} {D D' : Set ι}
    (h : DependsOn A D) (hDD : D ⊆ D') : DependsOn A D' :=
  fun ω η h' => h ω η fun i hi => h' i (hDD hi)

lemma dependsOn_coord {ι : Type*} (e : ι) : DependsOn {ω : ι → Bool | ω e = true} {e} :=
  fun ω η h => by rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h e rfl]

lemma chainOpen_dependsOn (u : V) (l : List A) :
    DependsOn {ω : G.edgeSet → Bool | ChainOpen ω u l} (subE u) := by
  induction l generalizing u with
  | nil => intro ω η _; simp [ChainOpen]
  | cons a rest ih =>
    intro ω η hagree
    simp only [Set.mem_setOf_eq, ChainOpen]
    constructor
    · rintro ⟨h, hω, hc⟩
      refine ⟨h, ?_, ?_⟩
      · have he : childE (⟨(u, a), h⟩ : Echild) ∈ subE u := childE_mem_subE (Pref.refl _) h
        rw [← hagree _ he]; exact hω
      · exact (ih (u.snoc a h)) ω η
          (fun i hi => hagree i (subE_mono (Pref.snoc u a h) hi)) |>.1 hc
    · rintro ⟨h, hω, hc⟩
      refine ⟨h, ?_, ?_⟩
      · have he : childE (⟨(u, a), h⟩ : Echild) ∈ subE u := childE_mem_subE (Pref.refl _) h
        rw [hagree _ he]; exact hω
      · exact (ih (u.snoc a h)) η ω
          (fun i hi => (hagree i (subE_mono (Pref.snoc u a h) hi)).symm) |>.1 hc

lemma fwd_dependsOn (u : V) (n : ℕ) :
    DependsOn {ω : G.edgeSet → Bool | Fwd ω u n} (subE u) := by
  have hset : {ω : G.edgeSet → Bool | Fwd ω u n} =
      ⋃ (l : {l : List A // l.length = n}), {ω | ChainOpen ω u l.1} := by
    ext ω
    constructor
    · rintro ⟨l, hl, hc⟩
      exact Set.mem_iUnion.2 ⟨⟨l, hl⟩, hc⟩
    · intro h
      obtain ⟨l, hc⟩ := Set.mem_iUnion.1 h
      exact ⟨l.1, l.2, hc⟩
  rw [hset]
  exact DependsOn.iUnion (D := subE u) (fun l => chainOpen_dependsOn u l.1)

lemma measurableSet_chainOpen (u : V) (l : List A) :
    MeasurableSet {ω : G.edgeSet → Bool | ChainOpen ω u l} := by
  induction l generalizing u with
  | nil => simp [ChainOpen]
  | cons a rest ih =>
    by_cases hv : u.Valid a
    · have hset : {ω : G.edgeSet → Bool | ChainOpen ω u (a :: rest)} =
          ({ω | ω (childE (⟨(u, a), hv⟩ : Echild)) = true} ∩
            {ω | ChainOpen ω (u.snoc a hv) rest}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ChainOpen]
        constructor
        · rintro ⟨h, h1, h2⟩
          refine ⟨?_, ?_⟩
          · rwa [show (⟨(u, a), h⟩ : Echild) = ⟨(u, a), hv⟩ from Subtype.ext rfl] at h1
          · rwa [show u.snoc a h = u.snoc a hv from V.ext rfl] at h2
        · rintro ⟨h1, h2⟩
          exact ⟨hv, h1, h2⟩
      rw [hset]
      exact (measurableSet_eq_fun (measurable_pi_apply _) measurable_const).inter
        (ih (u.snoc a hv))
    · have hset : {ω : G.edgeSet → Bool | ChainOpen ω u (a :: rest)} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, ChainOpen, Set.mem_empty_iff_false, iff_false]
        exact fun h => absurd h.1 hv
      rw [hset]; exact MeasurableSet.empty

lemma measurableSet_fwd (u : V) (n : ℕ) : MeasurableSet {ω : G.edgeSet → Bool | Fwd ω u n} := by
  have hset : {ω : G.edgeSet → Bool | Fwd ω u n} =
      ⋃ (l : {l : List A // l.length = n}), {ω | ChainOpen ω u l.1} := by
    ext ω
    constructor
    · rintro ⟨l, hl, hc⟩
      exact Set.mem_iUnion.2 ⟨⟨l, hl⟩, hc⟩
    · intro h
      obtain ⟨l, hc⟩ := Set.mem_iUnion.1 h
      exact ⟨l.1, l.2, hc⟩
  rw [hset]
  exact MeasurableSet.iUnion (fun l => measurableSet_chainOpen u l.1)

lemma chainOpen_take {ω : G.edgeSet → Bool} {u : V} :
    ∀ (l : List A), ChainOpen ω u l → ∀ n : ℕ, ChainOpen ω u (l.take n)
  | [], _, n => by simp [ChainOpen]
  | a :: rest, hc, 0 => by simp [ChainOpen]
  | a :: rest, hc, n + 1 => by
    obtain ⟨hv, h1, h2⟩ := hc
    exact ⟨hv, h1, chainOpen_take rest h2 n⟩

/-- The forward cluster reaches every depth. -/
def Cluster (ω : G.edgeSet → Bool) (u : V) : Prop := ∀ n, Fwd ω u n

lemma fwd_anti {ω : G.edgeSet → Bool} {u : V} {n : ℕ} (h : Fwd ω u (n + 1)) :
    Fwd ω u n := by
  obtain ⟨l, hlen, hc⟩ := h
  refine ⟨l.take n, by simp; omega, chainOpen_take l hc n⟩

lemma cluster_eq_iInter (u : V) :
    {ω : G.edgeSet → Bool | Cluster ω u} = ⋂ n, {ω | Fwd ω u n} := by
  ext ω
  simp only [Cluster, Set.mem_setOf_eq, Set.mem_iInter]

lemma cluster_anti (u : V) : Antitone (fun n => {ω : G.edgeSet → Bool | Fwd ω u n}) :=
  fun n m hnm ω hω => by
    obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    clear hnm
    induction k with
    | zero => simpa using hω
    | succ k ih => exact ih (fwd_anti hω)

end Ultra
