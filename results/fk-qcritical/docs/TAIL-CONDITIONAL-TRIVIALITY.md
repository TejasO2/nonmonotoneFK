# Tail conditional triviality and DLR Choquet decomposition

## Principal compiled results

- `ae_zeroOneOn_tailConditionalKernel/Law`: for a countable edge type and any
  monotone cofinal exterior filtration, almost every tail RCP fibre is
  simultaneously zero-one on the entire exterior tail. This needs no DLR
  hypothesis and no countably-generated-tail or properness premise.
- `isExtremalIn_dlr_iff_zeroOneOn_tail`: DLR simplex extremality is equivalent
  to exterior-tail triviality.
- `ae_isExtremalIn_dlr_tailConditionalLaw`: almost every tail fibre of an
  arbitrary DLR law is extremal DLR.
- `dlr_tailChoquet_decomposition`: combines that source-fibre extremality with
  the existing `tailLawDistribution` barycenter identity.
- `eq_dlr_of_extremal_unique`: if every extremal DLR law equals `μ₀`, then
  every DLR law in the class equals `μ₀`.
- `ae_mem_fkLimitMeasures_tailConditionalLaw`: removes the explicit
  fibre-extremality premise from the corresponding TailChoquet consequence.

The proof implements Theorem 15 of Berti--Rigo, *0--1 laws for regular
conditional distributions* (https://arxiv.org/pdf/math/0606604): countable
generating algebras, a tower/pullout covariance bound, backward L¹ convergence,
an a.e.-convergent subsequence, and symmetric-difference approximation. It
never takes an uncountable intersection of event-dependent null sets.

`ae_mem_fkLimitMeasures_tailConditionalLaw` concerns only that named class;
this work does not claim Theorem 1.4, 1.9, 1.10, or 1.11. The Choquet statement
uses the actual source fibres and the existing Giry barycenter. A separate
Giry-measurability proof for the extremal-DLR locus is not included; it is not
needed by `eq_dlr_of_extremal_unique`, which uses the actual source fibres.

No shared files were edited. The source imports the public
`FK.NewestModulesValidation` for the existing conditional uniqueness interface.

## Independent checks

The repository Elan toolchain is Lean 4.35.0. Both the full source compilation
and an independent `.olean` build succeeded. The audit source is
`TailConditionalTrivialityAudit.lean`; its captured output is
`TailConditionalTrivialityAudit.txt`. All audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
