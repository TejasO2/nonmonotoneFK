# Independent bond-star enhancement on the square lattice

`FK.SquareLatticeStar` constructs an independent, bounded-range local
enhancement on the actual `gridGraph`. It proves a strict comparison at the
explicit ordinary bond rate $p=1/8$, not a general essential-enhancement or
FK-window theorem.

## Ordinary law and percolation-free base

The graph is proved connected and locally finite with at most four neighbours
per vertex. The first-moment theorem therefore gives
`base_nonpercolating : percolationProb gridGraph origin baseRate = 0` at
`baseRate = 1/8`, since $4/8<1$. The origin and horizontal axis construct the
existing double-ray essentiality certificate
`originStar_essential : FK.AGImplant.DeviceEssential ...`; this is the
shared-activation double-ray interface, not the faulty general pivot surgery.

For each centre $v$, `starSupport v` consists precisely of the grid bonds
incident with $v$. The independent joint law

```lean
starLaw p s = FKLimit.bernoulliProduct
  (Sum.elim (fun _ : gridGraph.edgeSet => p) (fun _ : GridV => s))
```

puts independent rate-$p$ Bernoulli variables on edges and rate-$s$ variables
on star centres. `EnhancedRootEvent` is root percolation of the existing
`deviceConfig starSupport`, not a renamed constant or a critical-shift
hypothesis.

## Coarse aggregation and the Peierls input

The even sublattice is indexed by `coarse (x 0,x 1) = (2x 0, 2x 1)`. If two
adjacent coarse centres are activated, their two incident stars open the two
bonds through the lattice midpoint. This gives an actual two-step enhanced
walk. Induction over BBR paths proves that an infinite active coarse cluster
yields a genuine infinite enhanced cluster at the square-lattice origin.

The exact law identity

```lean
Measure.map coarseActive (starLaw p s) = BBR.sitePerc 2 s
```

comes from restricting the independent product along the injective even-site
embedding. All path and infinite-cluster measurability is proved. BBR's
Peierls result `pcSite_lt_one` then supplies some activation rate $0<s<1$ at
which ordinary coarse origin-cluster infinite probability is nonzero, and this
transfers to positive `EnhancedRootEvent` mass. The conclusion
`exists_interior_activation_strict_comparison` is exactly existential positive
probability, not probability one, an explicit numerical activation rate, or
an arbitrarily-small-activation/critical window. The argument is independent
of the ordinary bond parameter on the enhanced side, but the unenhanced base
comparison is stated only at $1/8$.

## Provenance and scope

The Peierls sources are from Tejasvi Singh Tomar's CC-BY-4.0 Zenodo software
record 23692474 v5: [DOI](https://doi.org/10.5281/zenodo.23692474).
The verified archive MD5 is `261b4e3738c8ce510f58788beb4e6827`.
The local source checksum equals that official file. `THIRD_PARTY.md` lists the
selected modules and local import-only adaptations; the full rerouting
development is not imported. The full licence is included.

All eleven BBR/BBRAG source closures plus the new lattice module and its audit
were rebuilt from scratch on Lean 4.35 with default heartbeats. The 17 reports
use only `propext`, `Classical.choice`, and `Quot.sound`.

This is a real special-case independent-product enhancement theorem. It is not
an `ActivationShift`, `RootShift`, `DeactivationShift` or general `hAG`, and
does not by itself prove Theorem 1.4, 1.10 or a source FK/DLR uniqueness
statement.
