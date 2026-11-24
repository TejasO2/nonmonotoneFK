Public modules: `FK.AGTree.{Reduced,Graph,Edges,Fwd,Model,Criterion,Shift,Main}`. Only module prefixes changed during integration. The ten principal declarations were independently rebuilt and axiom-audited. `enh_cluster_pos` gives a positive **forward-cluster** probability. It is not base nonpercolation, an exact critical point, quasi-transitivity, a full `OpenConnected` percolation interface, `hAG`, or a strict critical comparison.

# Direction 6 — activated two-class tree (m6, swarm smwu0pw30)

All files in `Ultra/`, Lean 4.35.0, compiled against the repository's read-only
`.lake` artifacts (Mathlib + `CurvatureVariance.Infra.EfronStein.Coordinates`);
no shared file, toolchain or dependency was modified.

    TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
    LEAN_PATH=$(cat $HOME/.fk_lean_path):$PWD $TC -o Ultra/X.olean Ultra/X.lean

Build order: `Reduced Graph Edges Fwd Model Criterion Shift Main` (8 modules,
~15 s each cold, 2–3 s warm). `Ultra/Audit.lean` reprints the axiom audits
(`audit-output.txt`): every principal declaration depends only on `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`/`admit`/custom axiom/`unsafe`.

## Construction (all in Lean)

`Ultra/Reduced.lean`, `Ultra/Graph.lean`:
* alphabet `A := Sum (Fin 3) (Fin 2)` with class map `acls : A → Fin 2`
  (class `0` = three "base" letters, class `1` = two "activation" letters);
* vertices = reduced words (no two equal adjacent letters); `G` is the resulting
  5-regular tree; `adj_iff` classifies edges as "append one letter" or "parent";
  `G_connected`, `bounded_degree` (at most 6 neighbours, in fact 5),
  noncomputable `G.LocallyFinite`.

`Ultra/Edges.lean`:
* `Echild := {p : V × A // p.Valid}`, `childE : Echild → G.edgeSet` is an
  explicit bijection (`childE_inj`, `childE_surj`, `edgeEquiv`), so every edge has
  a well-defined class `letterOf`;
* `law r := Measure.infinitePi (fun e => bernoulliMeasure true false (r (acls (letterOf e))))`
  is the independent product law with class-dependent rates;
* `measure_iInter_eq_prod`: for **any** `Measure.infinitePi` of probability
  measures and any finite family of events depending on pairwise disjoint
  coordinate blocks, the joint mass is the product of the masses.

`Ultra/Fwd.lean`: forward-cluster predicate `ChainOpen`/`Fwd`, `Cluster`,
measurability (`measurableSet_fwd`), subtree coordinate sets `subE` with
disjointness (`subE_snoc_disjoint`, `childE_notMem_subE_snoc…`), `DependsOn` for
subtrees (`fwd_dependsOn`), and antitonicity of the level events.

`Ultra/Model.lean`: **the branching recursion**

    pr r {ω | ¬ Fwd ω u (n+1)} = ∏ a : A, if h : u.Valid a then
        1 - r(class a) * pr r {ω | Fwd ω (u.snoc a h) n} else 1

(`measure_notFwd_succ`), `pr r A := (law r).real A`. This is the exact
finite-tree branching identity, proved from the block-independence lemma and the
disjointness of the children's subtrees.

`Ultra/Criterion.lean`: exact class counts of valid letters
(`card_valid_class`), `pr_mono`, and `pr_cluster_tendsto`
(level probabilities tend to the cluster probability).

`Ultra/Shift.lean`: **percolation criterion** `cluster_pos_of_uniform`: if
`0 ≤ w ≤ 1`, `0 ≤ c ≤ 1`, `(1-r_j)+r_j w_j ≤ c` for all `j`, `c^4 ≤ w` and
`c^5 < 1`, then `0 < pr r {Cluster root}`. Proof: induction that
`1 - pr{Fwd v n} ≤ w` (non-root) and `≤ c^5` (root) using
`#valid ≤ 5`, `#valid ≥ 4` off the root, `prod_ite_pow`, and monotone
convergence `pr_cluster_tendsto`.

`Ultra/Main.lean`: **`enh_cluster_pos`** — for the activated law with class-0
rate `3/10` and class-1 rate `1/2`, `0 < pr r {ω | Cluster ω V.root}`
(witnesses `w = 9/10`, `c = 97/100`: `24/25, 19/20 ≤ 97/100`,
`(97/100)^4 ≤ 9/10`, `(97/100)^5 < 1`).

## Scope and residuals (honest)

* What is proved: the exact local model, the exact branching recursion, the
  percolation criterion, and a concrete positive-probability percolation point
  of an inhomogeneous **two-rate** product model on a genuine 5-regular tree.
* **Not proved here**: (i) nonpercolation of the base law (a uniform
  first-moment induction `pr{Fwd v n} ≤ (3p)^n` was drafted and type-checked in
  parts but does not compile yet), hence no strict `p_c` comparison is asserted;
  (ii) quasi-transitivity: the letter-involution automorphisms are constructed
  on paper but their transitivity is **not** formalized in these files;
  (iii) exact critical parameters (the sharp two-type mean-matrix analysis),
  and the intended `hAG` instantiation.
* Nothing here is claimed to discharge `hAG`, Theorem 1.4/1.9/1.10/1.11, or any
  paper-level statement; `Cluster` is the combinatorial cluster of the tree
  model, and the identification of `Cluster` with `OpenConnected`-reachability
  of `FK.Percolating` is **not** carried out (only `Fwd ⇒` open-walk is
  immediate).
