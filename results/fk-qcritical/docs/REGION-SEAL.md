# Sealed-region free-boundary conditioning

Public module: `FK.RegionSeal`. This gives the finite free-boundary Markov
property for arbitrary finite labelled multigraphs and boundary setoids.

Let `U` be a vertex set, with internal labels having both endpoints in `U` and
all other labels external. Assume no nontrivial boundary block meets `U`, and
that the exterior configuration has no open external label touching `U`.
`connectionGraph_noCross` proves that ambient open connectivity never crosses
`U`; induced graphs identify with the free interior and the recorded exterior
`outGraph`. Consequently component counts and FK weights factor as an interior
term times an exterior-only factor (`componentCount_glue`, `fkWeight_glue`).

At interior parameters `0<p<1` and `0<q`, normalization yields
`fiberPMF_eq_region`: the law on internal coordinates obtained by normalizing
the FK weights on a prescribed sealed exterior fibre is exactly the free FK
law on the induced region graph. `fiberPMF_eq_region_of_closed_cut` is the
closed-cut form, `fiberPMF_eq_of_sealed` gives the two-coordinate comparison,
and `sealedPMF_eq_region` treats a nonempty finite set of sealed exteriors.
There is no block-decomposition or prescribed edge-order hypothesis.

The `fiberPMF` and `sealedPMF` definitions are normalized restrictions. The
development uses positivity to identify their weights, but does not separately
prove every conversion to `PMF.filter`. Endpoint parameters are not included.
This also does not instantiate an infinite-volume DLR conditional kernel, find
an adaptive random region, or assemble Lemma 2.1 or Theorem 5.1.

Thus this is a faithful local finite Markov/factorization result, not a
substitute for the remaining random-region and nested-box problems.
