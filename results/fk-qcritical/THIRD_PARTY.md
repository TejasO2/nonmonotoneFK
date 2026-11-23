# Vendored upstream sources

Only source modules on the import closure of `FK.lean` are copied. No upstream
comparator challenge or file containing a proof placeholder is imported.

| Namespace | Upstream repository | Commit | Included modules |
|---|---|---|---|
| `CurvatureVariance` | https://github.com/nitromannitol/FPP-variance (Scott Armstrong and Ahmed Bou-Rabee) | `cfe58d1d241d86bd831c2e1b3c61273200fb780b` | EfronStein/Coordinates and Percolation/{Product,Connections,Balls,Exploration,Critical} |
| `PercLib` | https://github.com/tomhutchcroft/perclib | `45309ab97e4f7ebd546b1d8485acc1ed421814ee` | Meta/Tag, Probability/ProdBernoulli, Probability/Coupling/Monotone |
| `OAI` | https://github.com/openai/math | `4eaee87548250b2682affda7d05d947c05554bae` | CriticalPercolation/Model, Entropy/Uniform01, ProductMeasure/{Density,BitMeasure,MonotoneBernoulli} |

All three projects are Apache-2.0 licensed. The corresponding license and notice
files are in `licenses/`. Existing copyright and adaptation headers are retained
in the Lean sources.

The project uses Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`.
