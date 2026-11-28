# Classical subcritical source uniqueness

This guide records the immediate subcritical consequences of the ordinary
comparison and nested equation (9). It distinguishes the completed parameter
branches from the full source statement, and does not use an enhancement or an
AG shift.

## The `q > 1` branch

`FK.ClassicalSubcriticalGt.sourceFKMeasures_singleton_of_one_lt_q_subcritical`
proves, for a countable locally finite connected simple graph and a supplied
root `o` and ordinary graph edge `e₀`, that if $1<q$, $0<p<1$, and
$p<p_c(G,o)$, then there is a unique member of the project's full
`SourceFKMeasures` family and that law is almost surely nonpercolating.

The countable-edge-set instance is explicit. `SourceFKMeasures` means the
source's arbitrary vertex-exhaustion weak limits with boundary conditions on
the actual boundary, together with every geometric all-finite-region source
DLR law. The seed edge `e₀` is used by
`exists_nonempty_sourceFKMeasure_tail` to choose a tail whose boxes have
nonempty edge types. These graph inputs must not be silently removed when
using the theorem, and no claim is made for arbitrary non-source conventions.

For $1<q$ and interior $p$ one has $p'<p$, hence
$\max(p,p')=p$. Proposition 4.2(2) is applied with both enhanced families
empty. Every separation, device and cardinality condition is then vacuous, and
`gtUpperParameters_empty` identifies its upper product literally with the
global Bernoulli product at $p$. The direction is explicitly
$\operatorname{Bernoulli}(p)\succeq\mu$ for every source family member $\mu$.

Separately, `ae_nonPercolating_globalUpper_of_one_lt_q` uses ordinary Bernoulli
subcriticality at the supplied root. The accepted arbitrary nested
`FK.Adaptive.NestedSumGeometry.sourceNestedEquationNine` gives the finite-volume
boundary error at the same ordinary rate, and
`theorem_1_10_modulo_AG_window_and_lemma_2_1` combines this estimate with
compactness and the source Choquet argument. Despite that helper's historical
name, this application supplies neither an AG window nor any enhanced device.

The additional declarations prove the rate identity, the empty-device profile
identity, product nonpercolation, full-source domination, and nonpercolation of
every individual source family member separately from the final singleton.

## Exact limits of the result

This is a genuine ordinary-subcritical uniqueness theorem for $q>1$, not an
enhanced critical-window conclusion. It requires $p<p_c(G,o)$ rather than
allowing a strict shift beyond $p_c$. It does not prove general AG, Theorem
1.4, the separate $q<1$ branch, an arbitrary common-dominant Theorem 5.1, or a
planar/supercritical theorem.

All six declarations are audited in the project-wide `Audit.lean`. The source
was rebuilt independently with pinned Lean 4.35, default heartbeats, and only
`propext`, `Classical.choice`, and `Quot.sound` in every axiom report. The
public gate remains `./check.sh` from `results/fk-qcritical`.
