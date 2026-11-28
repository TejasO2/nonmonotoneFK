# Classical subcritical source uniqueness

This guide records the immediate subcritical consequences of the ordinary
comparison and nested equation (9). The full source family is handled in the
interior parameter range of Theorem 1.9, for every positive `q`, without an
enhancement or an AG shift.

## Interior-parameter theorem for every positive `q`

The main declaration is

```lean
FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating
```

For a countable nonempty locally finite connected simple graph, a root `o`,
$0<p<1$, $0<q$, and

$$\max(p,p')<p_c(G,o),$$

it proves that there is a unique member of `SourceFKMeasures` and that its law
is almost surely nonpercolating. Here the literal upper rate is
`upperRateNN q p = max(p,p')`; for $q<1$ the subcriticality hypothesis is
therefore on $p'$, not incorrectly weakened to $p$. No seed edge or explicit
countable-edge-set premise appears in the final theorem. `SourceFKMeasures`
means the source's arbitrary vertex-exhaustion weak limits with actual
boundary conditions together with every geometric all-finite-region source
DLR law; arbitrary non-source conventions are not asserted.

The proof splits at $q=1$. For $q<1$, empty enhanced star/cycle families
specialize Proposition 4.2(1) to the ordinary upper product at $p'$, and
`canonicalSource_existsUnique_sourceFKMeasures` supplies the singleton from
the completed arbitrary nested equation (9). The $q=1$ branch transports the
proved `QOneLine` weak-limit and DLR classifications to the source family. For
$q>1$, $\max(p,p')=p$ and Proposition 4.2(2) supplies the ordinary
Bernoulli$(p)$ dominant. In both strict branches, an edge-free graph makes the
unique law directly nonpercolating, so an artificial seed-edge premise is not
needed. In each case the comparison direction is
$\operatorname{Bernoulli}(\max(p,p'))\succeq\mu$, and ordinary one-root
Bernoulli subcriticality makes the same controlling product nonpercolating.

This is the interior source-scope form of Theorem 1.9. It does not assert a
strict critical enhancement or any window above $p_c$.

## The `q > 1` branch helper

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

The all-$q$ theorem is genuinely an ordinary-subcritical source-family
uniqueness result at interior $0<p<1$, not an enhanced critical-window or
endpoint theorem. Its hypothesis remains $\max(p,p')<p_c(G,o)$, with a root
and connectedness for the one-root Bernoulli argument. It does not prove
general AG, Theorem 1.4 or 1.10, an arbitrary common-dominant Theorem 5.1, a
planar/supercritical theorem, or strong uniqueness for arbitrary non-source
boundary conventions.

The thirteen principal declarations across the two branch modules and the
all-$q$ assembly are audited in the project-wide `Audit.lean`. Their sources
were rebuilt independently with pinned Lean 4.35, default heartbeats, and
only `propext`, `Classical.choice`, and `Quot.sound` in every axiom report. The
public gate remains `./check.sh` from `results/fk-qcritical`.
