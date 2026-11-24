import FK.AGTree.Devices

/-!
# The two-class law is invariant under the word automorphisms

The single-letter automorphisms preserve the letter `letterOf` of every edge
(`Ultra/EdgeClass.lean`), hence the class function `acls ∘ letterOf` and the
edge rate `edgeRate r`.  This file

* extends the preservation to the word automorphisms `lmulListIso l`,
* proves that the independent two-class product law `law r` is invariant under
  the induced coordinate permutation (via
  `Measure.infinitePi_map_piCongrLeft`),
* shows that open connectivity and infinite clusters are transported by graph
  automorphisms, and
* concludes that the infinite-cluster probability is the same at every vertex:
  the two-class model is homogeneous on this quasi-transitive graph.
-/

namespace Ultra

open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

/-! ### Letter preservation for word automorphisms -/

lemma mapEdgeSet_lmulListIso_nil (e : G.edgeSet) :
    (lmulListIso ([] : List A)).mapEdgeSet e = e := by
  apply Subtype.ext
  rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
  have hfun : (⇑(lmulListIso ([] : List A)) : V → V) = id := rfl
  rw [hfun, Sym2.map_id]
  rfl

lemma mapEdgeSet_lmulListIso_cons (a : A) (t : List A) (e : G.edgeSet) :
    (lmulListIso (a :: t)).mapEdgeSet e =
      (lmulIso a).mapEdgeSet ((lmulListIso t).mapEdgeSet e) := by
  apply Subtype.ext
  rw [FK.QuasiTransitive.iso_coe_mapEdgeSet, FK.QuasiTransitive.iso_coe_mapEdgeSet,
    FK.QuasiTransitive.iso_coe_mapEdgeSet, Sym2.map_map]
  rfl

/-- Word automorphisms preserve the letter of every edge. -/
theorem letterOf_mapEdgeSet_lmulListIso (l : List A) (e : G.edgeSet) :
    letterOf ((lmulListIso l).mapEdgeSet e) = letterOf e := by
  induction l generalizing e with
  | nil => rw [mapEdgeSet_lmulListIso_nil]
  | cons a t ih =>
      rw [mapEdgeSet_lmulListIso_cons, letterOf_mapEdgeSet_lmulIso, ih]

/-- Consequently the two-class rate is invariant under the word automorphisms. -/
theorem edgeRate_mapEdgeSet_lmulListIso (r : Fin 2 → unitInterval) (l : List A)
    (e : G.edgeSet) :
    edgeRate r ((lmulListIso l).mapEdgeSet e) = edgeRate r e := by
  rw [edgeRate, edgeRate, letterOf_mapEdgeSet_lmulListIso]

/-! ### Invariance of the product law -/

/-- **The two-class product law is invariant under every class-preserving
automorphism**, in the coordinate-permutation form given by
`MeasurableEquiv.piCongrLeft`. -/
theorem law_map_perm (r : Fin 2 → unitInterval) (φ : G ≃g G)
    (hcls : ∀ e : G.edgeSet, letterOf (φ.mapEdgeSet e) = letterOf e) :
    (law r).map (MeasurableEquiv.piCongrLeft (fun _ => Bool) φ.mapEdgeSet) = law r := by
  have hμ : (fun i : G.edgeSet =>
        bernoulliMeasure true false (r (acls (letterOf (φ.mapEdgeSet i))))) =
      (fun i : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf i)))) := by
    funext i
    rw [hcls i]
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun i : G.edgeSet => bernoulliMeasure true false (r (acls (letterOf i))))
    (X := fun _ => Bool) (e := φ.mapEdgeSet)
  rw [hμ] at h
  exact h

/-- The same invariance for the word automorphisms. -/
theorem law_map_perm_lmulListIso (r : Fin 2 → unitInterval) (l : List A) :
    (law r).map (MeasurableEquiv.piCongrLeft (fun _ => Bool) (lmulListIso l).mapEdgeSet) =
      law r :=
  law_map_perm r (lmulListIso l) (letterOf_mapEdgeSet_lmulListIso l)

/-! ### Transport of open connectivity -/

/-- The configuration obtained from `ω` by moving every edge back along `φ`. -/
def permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) : G.edgeSet → Bool :=
  fun i => ω (φ.symm.mapEdgeSet i)

lemma eOf_mapEdgeSet {φ : G ≃g G} {u v : V} (h : G.Adj u v) :
    φ.mapEdgeSet (eOf h) = eOf (φ.toHom.map_adj h) := by
  apply Subtype.ext
  rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
  rfl

/-- Open adjacency is transported by an automorphism. -/
lemma oAdj_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) (u v : V) :
    OAdj (permConfig φ ω) (φ u) (φ v) ↔ OAdj ω u v := by
  constructor
  · rintro ⟨h, ho⟩
    have hh := φ.symm.toHom.map_adj h
    have h' : G.Adj u v := by simpa using hh
    refine ⟨h', ?_⟩
    have hval : (permConfig φ ω) (eOf h) = ω (eOf h') := by
      rw [permConfig, eOf_mapEdgeSet (φ := φ.symm) h]
      congr 1
      apply Subtype.ext
      simp
    rw [← hval]
    exact ho
  · rintro ⟨h, ho⟩
    refine ⟨φ.toHom.map_adj h, ?_⟩
    have hsame : eOf (φ.symm.toHom.map_adj (φ.toHom.map_adj h)) = eOf h := by
      apply Subtype.ext
      simp
    rw [permConfig, eOf_mapEdgeSet (φ := φ.symm) (φ.toHom.map_adj h), hsame]
    exact ho

/-- Open connectivity is transported by an automorphism. -/
theorem oReach_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) (v w : V) :
    OReach (permConfig φ ω) (φ v) (φ w) ↔ OReach ω v w := by
  constructor
  · intro h
    have h1 : OReach ω (φ.symm (φ v)) (φ.symm (φ w)) :=
      Relation.ReflTransGen.lift (φ.symm) (fun a b hab => by
        have := (oAdj_permConfig φ ω (φ.symm a) (φ.symm b)).mp (by simpa using hab)
        simpa using this) (φ v) (φ w) h
    rw [show φ.symm (φ v) = v from φ.symm_apply_apply v,
      show φ.symm (φ w) = w from φ.symm_apply_apply w] at h1
    exact h1
  · intro h
    exact Relation.ReflTransGen.lift (φ) (fun a b hab => by
      exact (oAdj_permConfig φ ω a b).mpr hab) v w h

/-- The open cluster of `φ v` in the permuted configuration is the image of the
open cluster of `v`. -/
theorem clusterSet_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) (v : V) :
    clusterSet (permConfig φ ω) (φ v) = φ '' clusterSet ω v := by
  ext x
  constructor
  · intro hx
    have hx' : OReach ω v (φ.symm x) := by
      have h1 : OReach ω (φ.symm (φ v)) (φ.symm x) :=
        Relation.ReflTransGen.lift (φ.symm) (fun a b hab => by
          have := (oAdj_permConfig φ ω (φ.symm a) (φ.symm b)).mp (by simpa using hab)
          simpa using this) (φ v) x hx
      rw [show φ.symm (φ v) = v from φ.symm_apply_apply v] at h1
      exact h1
    exact ⟨φ.symm x, hx', by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact (oReach_permConfig φ ω v u).mpr hu

/-- Infinite open clusters are preserved by automorphisms. -/
theorem infiniteClusterAt_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) (v : V) :
    InfiniteClusterAt (permConfig φ ω) (φ v) ↔ InfiniteClusterAt ω v := by
  rw [InfiniteClusterAt, InfiniteClusterAt, clusterSet_permConfig]
  exact Set.infinite_image_iff (fun x _ y _ h => φ.injective h)

/-! ### Homogeneity of the infinite-cluster probability -/

lemma permCongr_eq_permConfig (φ : G ≃g G) (ω : G.edgeSet → Bool) :
    (MeasurableEquiv.piCongrLeft (fun _ => Bool) φ.mapEdgeSet) ω = permConfig φ ω := by
  funext i
  have h := Equiv.piCongrLeft_apply_apply (fun _ => Bool) φ.mapEdgeSet ω
    (φ.mapEdgeSet.symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [MeasurableEquiv.coe_piCongrLeft]
  rw [h]
  rw [SimpleGraph.Iso.mapEdgeSet_symm_apply]
  rfl

/-- The forward cluster at the root is a measurable event. -/
theorem measurableSet_infiniteClusterAt_root :
    MeasurableSet {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} := by
  have hEq : {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} =
      {ω : G.edgeSet → Bool | Cluster ω V.root} := by
    ext ω
    exact (cluster_iff_infinite_root ω).symm
  rw [hEq, cluster_eq_iInter]
  exact MeasurableSet.iInter fun n => measurableSet_fwd V.root n

/-- Elementwise transport: the root cluster event in `ω` is the vertex-`v`
cluster event in the coordinate-permuted configuration. -/
theorem mem_cluster_iff_perm {v : V} {ω : G.edgeSet → Bool} :
    InfiniteClusterAt ω V.root ↔
      InfiniteClusterAt
        ((MeasurableEquiv.piCongrLeft (fun _ => Bool) (lmulListIso v.w).mapEdgeSet) ω) v := by
  rw [show (MeasurableEquiv.piCongrLeft (fun _ => Bool) (lmulListIso v.w).mapEdgeSet) ω
      = permConfig (lmulListIso v.w) ω from permCongr_eq_permConfig _ ω]
  have hφ : (lmulListIso v.w) V.root = v := lmulListIso_root v.red
  have h := infiniteClusterAt_permConfig (lmulListIso v.w) ω V.root
  rw [hφ] at h
  exact h.symm

/-- The coordinate permutation of `lmulListIso v.w` pulls the vertex-`v`
cluster event back to the root cluster event. -/
theorem preimage_infiniteClusterAt (v : V) :
    (MeasurableEquiv.piCongrLeft (fun _ => Bool) (lmulListIso v.w).mapEdgeSet) ⁻¹'
      {ω : G.edgeSet → Bool | InfiniteClusterAt ω v} =
      {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} := by
  ext ω
  rw [Set.mem_preimage]
  exact (mem_cluster_iff_perm (v := v) (ω := ω)).symm

/-- **The infinite-cluster event is measurable at every vertex**, because the
word automorphism `lmulListIso v.w` carries it to the root event. -/
theorem measurableSet_infiniteClusterAt (v : V) :
    MeasurableSet {ω : G.edgeSet → Bool | InfiniteClusterAt ω v} := by
  have key : {ω : G.edgeSet → Bool | InfiniteClusterAt ω v} =
      (MeasurableEquiv.piCongrLeft (fun _ => Bool) (lmulListIso v.w).mapEdgeSet).symm ⁻¹'
        {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} := by
    ext x
    rw [Set.mem_preimage]
    have h := mem_cluster_iff_perm (v := v)
      (ω := (MeasurableEquiv.piCongrLeft (fun _ => Bool) (lmulListIso v.w).mapEdgeSet).symm x)
    rw [MeasurableEquiv.apply_symm_apply] at h
    exact h.symm
  rw [key]
  exact measurableSet_infiniteClusterAt_root.preimage (MeasurableEquiv.measurable _)

/-- **Homogeneity.**  The probability that the open cluster of `v` is infinite
is independent of `v`. -/
theorem pr_infiniteClusterAt_eq_root (r : Fin 2 → unitInterval) (v : V) :
    pr r {ω : G.edgeSet → Bool | InfiniteClusterAt ω v} =
      pr r {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} := by
  have hAv := measurableSet_infiniteClusterAt v
  have hmap := law_map_perm_lmulListIso r v.w
  have h1 : ((law r).map
        (MeasurableEquiv.piCongrLeft (fun _ => Bool) (lmulListIso v.w).mapEdgeSet)).real
        {ω : G.edgeSet → Bool | InfiniteClusterAt ω v} =
      (law r).real {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply (MeasurableEquiv.measurable _) hAv, preimage_infiniteClusterAt]
  rw [pr, pr]
  conv_lhs => rw [← hmap]
  exact h1

/-! ### Uniformity of the two-class percolation probabilities -/

/-- **Uniform vanishing of the base infinite-cluster probability.**  At base
rate `3/10` with activation `0`, every vertex has infinite-cluster probability
zero, not only the root. -/
theorem base_nonpercolation_uniform (v : V) :
    pr (enhRate p0 0) {ω : G.edgeSet → Bool | InfiniteClusterAt ω v} = 0 := by
  rw [pr_infiniteClusterAt_eq_root]
  have hmono : pr (enhRate p0 0) {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} ≤
      pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} :=
    pr_mono _ (fun ω hω => ⟨V.root, hω⟩)
  have h0 : pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} = 0 := base_nonpercolation
  linarith [pr_nonneg (enhRate p0 0) {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root}]

/-- **Uniform positivity of the activated infinite-cluster probability.**  At
rates `(3/10, 1/2)` every vertex has strictly positive infinite-cluster
probability. -/
theorem activated_percolation_uniform (v : V) :
    0 < pr (enhRate p0 s0) {ω : G.edgeSet → Bool | InfiniteClusterAt ω v} := by
  rw [pr_infiniteClusterAt_eq_root]
  have hmono : pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Cluster ω V.root} ≤
      pr (enhRate p0 s0) {ω : G.edgeSet → Bool | InfiniteClusterAt ω V.root} :=
    pr_mono _ (fun ω hω => cluster_infinite hω)
  linarith [enh_cluster_pos]

end Ultra
