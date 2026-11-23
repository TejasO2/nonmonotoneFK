# Noncoherent fixed-source counterexample

`NoncoherentCounterexample.lean` proves a precise obstruction to deriving
geometric DLR membership from an unrestricted arbitrary-boundary `IsFKLimit`
plus `GlobalAtMostOne` under the current public definitions.

The example is the complete simple graph on `{false,true}`, with its unique edge
and the constant exhaustion by the exhaustive one-edge box. At `q=2`, `p=1/2`,
the constant finite-volume sequence with the fully wired setoid is an actual
`IsFKLimit`. Finiteness proves global uniqueness and exterior uniqueness. Yet
this limit is not DLR for the canonical free geometric assignment, and, by the
accepted convention-transport theorem, it is not DLR for any assignment
satisfying `IsGeometric` for the same box data.

The direct certificate is exact. In the exhaustive box, DLR forces the interior
marginal to be the finite FK law at the unique exterior. The all-open FK masses
are `1/3` with free boundary and `1/2` with fully wired boundary. This is not a
claim that the graph is infinite, that the paper's intended theorem is false,
or that coherent/geometric weak-limit theorems fail. It shows that an
unrestricted fixed-source assertion in the present API needs an additional
hypothesis (such as a geometric/coherent restriction). It also does not
construct the induced genuinely noncoherent local DLR data on infinite graphs.

The module uses public `FK.*` imports, default heartbeats, no `sorry`, `admit`,
`unsafe`, or custom axioms. Its `#print axioms` output is in `audit.log`.
Build and audit with `./build_and_audit.sh`.

## Source comparison and verification

The paper's [Proposition 1.8 and its convention
setup](https://arxiv.org/html/2512.16486v1#S1.Thmproposition8) begins with an
infinite connected locally finite graph. This example is finite and concerns
only the unrestricted formal assertion, so it is not recorded as an error in
the paper. A broader library sweep must preserve whatever geometric/coherent
hypotheses are actually used.

The source independently elaborated with the repository's pinned Lean 4.35.0
toolchain at default heartbeats. Its thirteen principal audits were added to
`Audit.lean`; each reports only `propext`, `Classical.choice`, and `Quot.sound`.
The integrated `check.sh` verifies the whole build, all audits, documentation
links, and the placeholder/forbidden-declaration scan.
