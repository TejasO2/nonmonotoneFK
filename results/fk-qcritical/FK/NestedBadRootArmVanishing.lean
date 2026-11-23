import FK.NestedBadRootAttachment

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal Topology unitInterval Sym2 SimpleGraph

/-!
# Fixed-root arm vanishing and conditional FK-limit equality

The per-scale split, endpoint, `hgood`, and bad-only root-attachment
certificates remain inputs. These are centered weak-limit results, not a
whole-ball radial argument or a general strong-uniqueness theorem.
-/


namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- **Bad-only fixed-root errors vanish under nonpercolation.**

At scale `n`, the smaller and larger boxes are genuine centered metric boxes of
radii `r n` and `N n`.  The displayed `hroot` premise attaches the left split
vertices to the *same* finite root set only on configurations outside the
maximal split stratum.  The right vertices lie outside radius `n + L`, while
`n + L ≤ N n` gives finite coordinate support in the larger box.  The common
upper Bernoulli law is almost-surely nonpercolating by `hμ`.

Every one-scale `hgood` identity is retained as input.  Consequently this is a
conditional vanishing theorem for the actual metric-box cylinder errors, not a
proof of the missing coupling identity or of strong uniqueness. -/
theorem metricBox_cylinder_abs_sub_tendsto_zero_of_good_of_bad
    [Countable V] [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool))
    (N r : ℕ → ℕ) (L : ℕ)
    (hnN : ∀ n, n + L ≤ N n) (hrN : ∀ n, r n ≤ N n)
    (α : ∀ n, (metricBox hG o (N n)).BoundaryPartition)
    (β : ∀ n, (metricBox hG o (r n)).BoundaryPartition)
    (hJD : ∀ n, J ⊆ (metricBox hG o (r n)).edges)
    {m k : ℕ → ℕ} {U K : ℕ → Type*}
    [∀ n, Fintype (U n)] [∀ n, Fintype (K n)]
    (si : ∀ n, Fin (m n) → U n) (ti : ∀ n, Fin (m n) → U n)
    (so xo : ∀ n, Fin (k n) → U n ⊕ K n)
    (d : ∀ n, Fin (m n) ⊕ Fin (k n) ≃
      Fin (Fintype.card (metricBox hG o (r n)).edges))
    (f : ∀ n, U n ⊕ K n → V)
    (hend : ∀ n a,
      s(f n ((ambientOfSum (splitSource (si n) (so n))
          (splitTarget (ti n) (xo n))).source a),
        f n ((ambientOfSum (splitSource (si n) (so n))
          (splitTarget (ti n) (xo n))).target a)) =
        ((edgeIndex (metricBox hG o (r n)) (d n a)).1).1)
    (roots : Finset V)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hfar : ∀ n k, n + L ≤ G.dist o (f n (Sum.inr k)))
    (hroot : ∀ n z, (restrictΔ (metricNestedEquiv hG o (hrN n)) z ∘ d n) ∉
      maximalSplitStratum (si n) (ti n) (so n) (xo n) → ∀ u, ∃ a ∈ roots,
      OpenConnected G ((metricBox hG o (N n)).glue
        ((metricBox hG o (N n)).closedExterior,
          (metricBox hG o (N n)).reindex (edgeIndex _) z)) Set.univ a
        (f n (Sum.inl u)))
    (hgood : ∀ n,
      let C : Set (((metricBox hG o (r n)).indexedGraph
          (edgeIndex _)).Configuration) :=
        (fun ρ : ((metricBox hG o (r n)).indexedGraph
          (edgeIndex _)).Configuration => ρ ∘ d n) ⁻¹'
            maximalSplitStratum (si n) (ti n) (so n) (xo n)
      let t := metricNestedTriple hG o (hrN n) (α n) (β n) hq hp₀ hp₁
      let BS := metricBox hG o (N n)
      let e := metricNestedEquiv hG o (hrN n)
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S ((hJD n).trans (nested_metricBox_edges hG o (hrN n)))) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S ((hJD n).trans (nested_metricBox_edges hG o (hrN n)))) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)))
    (hμ : ∀ᵐ ω ∂(percolation G
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))),
      ω ∈ FK.NonPercolating G) :
    Tendsto (fun n =>
      |((metricBox hG o (N n)).finiteVolumeLaw hq hp₁.le (α n) :
            Measure (Configuration G.edgeSet)).real (cylinder J S) -
        ((metricBox hG o (r n)).finiteVolumeLaw hq hp₁.le (β n) :
            Measure (Configuration G.edgeSet)).real (cylinder J S)|)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_measureReal_finiteRootArms_of_ae_nonPercolating hG
      (percolation G (unitOfNN (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le))) roots hμ)
  · exact Eventually.of_forall fun n => abs_nonneg _
  · exact Eventually.of_forall fun n =>
      metricBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad
        hG o hq hp₀ hp₁ J S (hnN n) (hrN n) (α n) (β n) (hJD n)
        (si n) (ti n) (so n) (xo n) (d n) (f n) (hend n)
        roots hA (hfar n) (hroot n) (hgood n)

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.metricBox_cylinder_abs_sub_tendsto_zero_of_good_of_bad


namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- **FK-limit equality from bad-only root attachment.**

For each finite observation base `J`, the root set `roots J` and hence the
width `dataWidth G o J (roots J)` are fixed.  At arm radius `m`, the smaller
metric box has radius `m + dataWidth`; every sufficiently large metric box is
used on the other side.  The supplied split has its right vertices beyond
exactly that smaller-box radius, and `hroot` is required only off its maximal
stratum.

The hypotheses `hgood` and `hroot` are substantive per-scale inputs.  Under
those inputs and zero Bernoulli percolation at the common upper rate, the two
actual centered-exhaustion FK weak limits are equal.  This is not the general
ordinary-nested-box theorem: its split presentations and bad-only attachment
certificates remain to be constructed. -/
theorem eq_of_isFKLimit_metricBox_of_nested_good_of_bad_rootAttached
    [Countable V] [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α β : ∀ n, (metricBox hG o n).BoundaryPartition)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le α μ)
    (hν : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le β ν)
    (hzero : ∀ x, percolationProb G x
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)) = 0)
    (roots : Finset G.edgeSet → Finset V)
    {mI kO : Finset G.edgeSet → ℕ → ℕ → ℕ}
    {U K : Finset G.edgeSet → ℕ → ℕ → Type*}
    [∀ J m n, Fintype (U J m n)] [∀ J m n, Fintype (K J m n)]
    (si : ∀ J m n, Fin (mI J m n) → U J m n)
    (ti : ∀ J m n, Fin (mI J m n) → U J m n)
    (so xo : ∀ J m n, Fin (kO J m n) → U J m n ⊕ K J m n)
    (d : ∀ J m n, Fin (mI J m n) ⊕ Fin (kO J m n) ≃
      Fin (Fintype.card (metricBox hG o
        (m + dataWidth G o J (roots J))).edges))
    (f : ∀ J m n, U J m n ⊕ K J m n → V)
    (hend : ∀ J m n a,
      s(f J m n ((ambientOfSum (splitSource (si J m n) (so J m n))
          (splitTarget (ti J m n) (xo J m n))).source a),
        f J m n ((ambientOfSum (splitSource (si J m n) (so J m n))
          (splitTarget (ti J m n) (xo J m n))).target a)) =
        ((edgeIndex (metricBox hG o (m + dataWidth G o J (roots J)))
          (d J m n a)).1).1)
    (hfar : ∀ J m n k,
      m + dataWidth G o J (roots J) ≤ G.dist o (f J m n (Sum.inr k)))
    (hroot : ∀ J m n
      (hrn : m + dataWidth G o J (roots J) ≤ n) z,
      (restrictΔ (metricNestedEquiv hG o hrn) z ∘ d J m n) ∉
        maximalSplitStratum (si J m n) (ti J m n) (so J m n) (xo J m n) →
      ∀ u, ∃ a ∈ roots J,
        OpenConnected G ((metricBox hG o n).glue
          ((metricBox hG o n).closedExterior,
            (metricBox hG o n).reindex (edgeIndex _) z)) Set.univ a
          (f J m n (Sum.inl u)))
    (hgood : ∀ (J : Finset G.edgeSet) (S : Set (J → Bool)) (m n : ℕ)
      (hrn : m + dataWidth G o J (roots J) ≤ n),
      let C : Set (((metricBox hG o
          (m + dataWidth G o J (roots J))).indexedGraph
          (edgeIndex _)).Configuration) :=
        (fun ρ : ((metricBox hG o
          (m + dataWidth G o J (roots J))).indexedGraph
          (edgeIndex _)).Configuration => ρ ∘ d J m n) ⁻¹'
            maximalSplitStratum (si J m n) (ti J m n) (so J m n) (xo J m n)
      let t := metricNestedTriple hG o hrn (α n)
        (β (m + dataWidth G o J (roots J))) hq hp₀ hp₁
      let BS := metricBox hG o n
      let e := metricNestedEquiv hG o hrn
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J (roots J) m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J (roots J) m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C))) :
    μ = ν := by
  let ρ : ProbabilityMeasure (G.edgeSet → Bool) :=
    ⟨percolation G (unitOfNN (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le)), inferInstance⟩
  refine probabilityMeasure_eq_of_nested_finiteRootArm_bounds_reindexed hG
    (fun n => (metricBox hG o n).finiteVolumeLaw hq hp₁.le (α n))
    (fun n => (metricBox hG o n).finiteVolumeLaw hq hp₁.le (β n)) μ ν ρ
    hμ hν ?_ roots (fun J m => m + dataWidth G o J (roots J)) ?_ ?_
  · change ∀ᵐ ω ∂(percolation G
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))),
      ω ∈ FK.NonPercolating G
    exact NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero _ hzero
  · intro J
    exact tendsto_add_atTop_nat (dataWidth G o J (roots J))
  · intro J S m
    filter_upwards [eventually_ge_atTop (m + dataWidth G o J (roots J))] with n hn
    exact metricBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad
      hG o hq hp₀ hp₁ J S hn hn (α n)
      (β (m + dataWidth G o J (roots J)))
      (base_subset_smaller_metricBox hG o J (roots J) m)
      (si J m n) (ti J m n) (so J m n) (xo J m n) (d J m n) (f J m n)
      (hend J m n) (roots J)
      (fun a ha => dist_le_dataWidth G o J ha) (hfar J m n)
      (hroot J m n hn) (hgood J S m n hn)

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.eq_of_isFKLimit_metricBox_of_nested_good_of_bad_rootAttached
