# Punctured finite lattice boxes

Public module: `FK.LatticeBoxes` (namespace `LatticeBoxes`, importing the
pinned Mathlib only). For original vertices `Fin d → ℤ` with nearest-neighbour
lattice bonds and centered integer $\ell^\infty$ boxes, deleting any prescribed
vertex leaves the induced box graph preconnected whenever $d\ge2$.

`exists_box_walk_avoiding` constructs an ordinary lattice walk with every
support vertex in the box. The strong induction on taxicab distance either
makes progress toward the target or replaces it with an explicit small square
detour. The code handles the second-coordinate and terminal-avoidance cases
rather than merely appealing to Menger's theorem. `puncturedBox_preconnected`
and `reachable_induce_box_diff_singleton` transport this walk to the induced
box-minus-singleton graph.

This is the geometric connectivity input used by balanced lattice pivotal
linkages. It does **not** prove four-terminal disjoint linkage, finite-fibre
pivot transport, total Bernoulli-profile influence comparisons, or a general
quasi-transitive essential-enhancement shift. No critical-point or FK theorem
is promoted from this module.
