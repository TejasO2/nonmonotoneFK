# Arbitrary-boundary nested interior factorization

## Deliverable

`NestedArbitraryInterior.lean` compiles under the repository's pinned Lean
4.35.0 environment with default heartbeats. Its two pinned imports are
`FK.ExteriorMarkov` and `FK.WiredRightInterior`; no source from the accepted
`NestedFiniteCoupling.lean` artifact is copied or modified.

## Proved statements

1. For every finite labelled graph with edges split into interior `I` and
   exterior `O`, and **every** ambient boundary setoid `ζ`, `fixedGraph` keeps
   `ζ`, all exterior-open edges, and no interior-open edges. Its reachability
   relation defines `effectiveBoundary`.
2. `reachable_wiredGluedGraph_iff` identifies reachability in the full graph
   with reachability in the interior graph using this effective boundary.
   `componentCount_glue` and `fkWeight_glue` give exact component-count and
   unnormalized-FK-weight factorizations. There is no no-cross assumption:
   left-left, right-right, and cross relations are all present in `ζ`.
3. `conditionedPMF_fkPMF` and `filter_fkPMF_eq_map_glue` identify the actual
   exterior-fiber `PMF.filter` with the pushforward of the actual interior FK
   law at `effectiveBoundary`, for `0 < q` and `0 < p < 1`.
   `effectiveBoundary_free` shows exact specialization to the integrated
   `exteriorBoundary` construction.
4. `filter_fkPMF_eq_of_effectiveBoundary_eq` gives a precise graph-theoretic
   compatibility condition for two arbitrarily cross-wired boundaries. It does
   not assert that two unrelated setoids have the same conditional law.
5. The second namespace treats a separated split graph with `sumBoundary θ ζ`.
   Here `θ` is an arbitrary shared left setoid, not necessarily free, and the
   right setoid is arbitrary. The proofs give an exact graph sum, component
   count, FK weight factorization, and filtered region-`θ` law.
6. `filter_twoSided_eq_of_mem_maximalSplitStratum` uses the canonical actual
   `maximalSplitStratum` membership (via its separation equivalence and
   `ExteriorHasRight`) to prove equality of the two filtered configuration PMFs
   for independently arbitrary right setoids `ζ` and `η`, retaining the shared
   arbitrary left setoid `θ`.

## Verification

Run from `results/fk-qcritical` with repo Elan at `../../.scratch/elan`:

```bash
lake env lean /absolute/path/to/.ultramath/smwsv3inm/m1/NestedArbitraryInterior.lean
```

`build.log` records the successful run and the exact `#print axioms` output.
The ten principal declarations audited there use only `propext`,
`Classical.choice`, and `Quot.sound`. The file contains no `sorry`, `admit`,
`unsafe`, or new `axiom` declaration.

## Explicit residual gaps

- This does **not** yet prove the `hgood` premise of
  `fkNestedOrderedTriple_abs_sub_le_of_good`. The new results are exact
  exterior-fiber and maximal-stratum laws; their transport through the common
  upper sequential/nested coupling remains to be done.
- In the two-sided split theorem, cross-summand setoid relations are excluded
  explicitly by `sumBoundary`. Fully arbitrary cross wiring is covered by the
  effective-boundary theorem, but comparison of two such laws requires their
  effective boundaries to agree. No unsupported universal free-interior or
  good-intersection claim is made for unrelated cross setoids.
- No nested-box edge equivalence is constructed here; no equation-(9)
  instantiation, vanishing-arm estimate, DLR uniqueness theorem, or named-paper
  theorem is claimed.
