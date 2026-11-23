# Start here: reading and working on the repository

## 1. Establish the claim before following a proof

Read [PROOF-STATUS.md](PROOF-STATUS.md) first. Theorems 1.4, 1.10, and 1.11
are not yet established as whole results. A declaration with a paper name may
be an intentionally conditional reduction. The documentation strings on those
declarations distinguish them; the older Proposition 4.2 names in `FKLimit` are
specifically marked **legacy opposite-sandwich reductions**, not the paper API.

The mathematical source is Vincent Beffara, Corentin Faipeur, and Tejas Oke,
[A New Bound for the Critical Point of the FK Model for q < 1, arXiv:2512.16486v1](https://arxiv.org/abs/2512.16486).
Its sections 3–5 are the main formalization targets. Compiling a theorem
establishes its Lean statement; fidelity to the paper must be checked separately
against that source.

## 2. Read the model, not just theorem names

The project uses several deliberately distinct representations:

- `FK.Finite.LabelledMultigraph` in `FK/FiniteModel.lean` retains edge labels,
  parallel edges, loops, and arbitrary boundary setoids. Its `fkPMF`/`fkMeasure`
  are the normalized finite FK laws; they are not generic weights.
- A configuration in that part is `E → Bool`. The older open-path API uses
  `Fin 2` bits. Conversion functions such as `configToBool` and `configOfBool`
  are explicit; equalities built from them are meaningful interfaces, not
  graph coercions to ignore.
- `p` is the FK edge weight and `FK.prime q p` is
  $p/(p+q(1-p))$. The unit-interval type `I` and its coercions to `Real` are
  explicit in the enhanced-dynamics files.
- `FKLimit.StochasticallyDominates ν μ` means **ν dominates μ**:
  `μ A ≤ ν A` for measurable increasing `A`. New code should use the oriented
  bridges in `FK/MainIntegration.lean`.
- `FKEnhancement`-namespace finite laws are finite probability objects
  `OpenPath.FinProb`; `.toPMF` and `.toMeasure` convert them into Mathlib
  probability and measure types. Distinguish these from the actual ambient
  measure on all infinite configurations.


For closed-cutset enhancement, `HasClosedCutset`, `CutsetFamily`, and
`certificateEvent` are the central definitions. For open-path enhancement, use
`HasEnhancingPaths`, `AuxiliaryPaths`, and `SomePathOpen`. A positive arithmetic
bonus is only useful after its graph-theoretic certificate and enhanced
comparison are supplied.

## 3. Read in dependency order

For the finite model, follow:

1. `FK/FiniteModel.lean`: labelled graphs, component counts, FK weights and PMFs.
2. `FK/FiniteFiber.lean` and `FK/ComponentUpdate.lean`: off-edge fibers and
   component-change calculations.
3. `FK/FiniteConditional.lean` and `FK/FiniteComparison.lean`: singleton FK
   conditionals, equations (2) and (3).
4. `FK/Glauber.lean` and `FK/FKGlauber.lean`: exact heat-bath updates,
   stationarity and convergence.

For the enhanced cutset comparison, continue with:

5. `FK/Proposition31All.lean`, `FK/MultigraphEnhancement.lean`, and
   `FK/ClosedCutsetBridge.lean`: rates, certificates, triple updates and bridges.
6. `FK/LowerCutsetChain.lean` and `FK/LowerCutsetComparison.lean`: the lower
   enhanced comparison for $p \lt p'$.
7. `FK/UpperCutsetChain.lean` and `FK/UpperCutsetComparison.lean`: the reverse
   comparison for $p' \lt p$.

The key construction is summarized in the root docstring of each comparison
module. The outer ordered pair starts in its stationary product law. FK starts
at the appropriate ordinary marginal and converges by the separately proved FK
Glauber convergence theorem. No full-support claim about the singular ordered
pair is made.

For exploration and uniqueness infrastructure, see [MODULES.md#uniqueness-and-exploration](MODULES.md#uniqueness-and-exploration).
For planar duality and critical windows, see [MODULES.md#duality-phases-and-critical-windows](MODULES.md#duality-phases-and-critical-windows).

To read the assembled finite theorem: `FK/Theorem12Less.lean` gives strict
closed-cutset lower and open-path upper enhancement for $0\lt q\lt1$;
`FK/Theorem12Greater.lean` gives the reverse mixed direction for $1\lt q$.
The four dynamic propositions and their canonical wrappers are in
`FK/CanonicalDynamics.lean`.

For reverse conditioning, `FK/BackwardConditional.lean` supplies the decreasing
filtration $L^2$/$L^1$ projection result. The theorem from eventual agreement
of exterior conditional probabilities still needs its DLR, extremality and
measurable-marginal inputs; full uniqueness is not inferred merely from that
convergence theorem.

## 4. Reproduce checks

Install Elan and Lake using the standard Lean instructions, then run from the
repository root:

```sh
lake exe cache get
./check.sh
```

The `lean-toolchain` file causes Elan to select Lean 4.35.0. Do not replace it
with an arbitrary globally installed Lean. No dependency upgrade or
`lake update` is needed. Compiled `.lake/` files, Elan installations, and local
scratch directories are not part of the source project.

To check one module:

```sh
lake env lean FK/LowerCutsetComparison.lean
```

To inspect a declaration and its exact type, create a separate local `.lean`
file containing, for example,

```lean
import FK

#check FKEnhancement.graphConnectionEvent_lower_comparison
#print axioms FKEnhancement.graphConnectionEvent_lower_comparison
```

and run `lake env lean YourFile.lean` from the repository. `#print axioms` tests
the proof's axiomatic dependencies, not the mathematical fidelity of its
statement. `Audit.lean` is a selected audit surface, not a list of all definitions.

## 5. Add or change proofs

Keep new modules under `FK/`, import them from `FK.lean` if they are part of the
public build, and add meaningful principal declarations to `Audit.lean`. Do not
turn a missing mathematical input from the paper into a new explicit assumption
without documenting it as conditional. In particular, do not supply a limiting
law, stationary equation, or ordered coupling that is intended to be constructed.

Use concrete off-edge marginals and event-level inequalities rather than the
reverse stochastic convention found in older APIs. Preserve edge labels and
boundary setoids; changing to an arbitrary simple graph can invalidate the
claimed relation to the wired FK model.

Temporary Lean experiments do not count as proved code. Never commit `sorry`,
`admit`, new axioms, or `unsafe` declarations to evade an obligation. Warnings
from code modernization are different from elaboration errors, but all changes
must pass `./check.sh` at the end.

## Directory conventions

Authoritative proof sources are `FK/*.lean`, the root `FK.lean`, and
`Audit.lean`. Documentation is in `docs/`. Vendored dependency source closures
are under `CurvatureVariance/`, `PercLib/`, and `OAI/`; their commit pins and
licenses are in `THIRD_PARTY.md` and `licenses/`. For dependency edits, preserve
upstream copyright and prefer fixing the FK-side adapter with a minimal,
well-documented patch.
