# Vendored upstream sources

Only source modules on the import closure of `FK.lean` are copied. No upstream
comparator challenge or file containing a proof placeholder is imported.

| Namespace | Upstream repository | Commit | Included modules |
|---|---|---|---|
| `CurvatureVariance` | https://github.com/nitromannitol/FPP-variance (Scott Armstrong and Ahmed Bou-Rabee) | `cfe58d1d241d86bd831c2e1b3c61273200fb780b` | EfronStein/Coordinates and Percolation/{Product,Connections,Balls,Exploration,Critical} |
| `PercLib` | https://github.com/tomhutchcroft/perclib | `45309ab97e4f7ebd546b1d8485acc1ed421814ee` | Meta/Tag, Probability/ProdBernoulli, Probability/Coupling/Monotone |
| `OAI` | https://github.com/openai/math | `4eaee87548250b2682affda7d05d947c05554bae` | CriticalPercolation/Model, Entropy/Uniform01, ProductMeasure/{Density,BitMeasure,MonotoneBernoulli} |

The three projects above are Apache-2.0 licensed. The corresponding license and notice
files are in `licenses/`. Existing copyright and adaptation headers are retained
in the Lean sources.

## Square-lattice Peierls sources

Tejasvi Singh Tomar, *Lean formalization for: Essential enhancements of site
percolation in every dimension and on periodic lattices*, Zenodo software record
23692474, version v5, 2026-10-27,
https://doi.org/10.5281/zenodo.23692474. The official software metadata declares
**CC-BY-4.0**. The complete upstream archive has size 2,707,999 bytes and MD5
`261b4e3738c8ce510f58788beb4e6827`, matching the verified local archive.

Selected source modules are `BBR/{Defs,Basic,Layers}` and
`BBRAG/{Defs,Parity,Timar,Shell,Animals,Box,Measure,Peierls}`. They provide the
independent product-site law and the Peierls proof `BBR.pcSite_lt_one` used by
`FK.SquareLatticeStar`. The unrelated rerouting/essential-enhancement part of the
upstream project is outside this selected closure. No claim to import the full
upstream development is intended.

Local adaptation, beyond the selection itself: `BBRAG/Defs.lean` imports only
`BBR.Layers`; `BBRAG/Measure.lean` retains the percolation-law definitions
needed for the Peierls theorem without importing the unrelated rerouting
development; `BBRAG/Shell.lean` supplies explicit set arguments to its
`ContainsPath.mono` application. The other selected source files are unchanged.
The sources were rebuilt against this repository's Lean 4.35.0 and pinned
Mathlib. The official license text is in `licenses/CC-BY-4.0.txt`. This is
attribution, not an endorsement by the upstream author.

The project uses Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`.
