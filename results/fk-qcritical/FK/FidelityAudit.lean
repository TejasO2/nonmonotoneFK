import FK.InteriorWeakLimit
import FK.Proposition42Interior
import FK.WeakLimitCylinderTransport
import FK.AGEdgeGadget
import FK.ThetaDuality
import FK.PlaneCutCircuit

/-! Independent axiom surface for the source-fidelity review in this directory. -/

-- Interior weak-limit closure and transport.
#print axioms FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.integral_reconstruct
#print axioms FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.tendsto_reconstruct
#print axioms FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.isDLR_of_tendsto
#print axioms FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.continuous_conditionalLaw_of_isLocallyConstant
#print axioms FK.InfiniteVolume.InteriorWeakLimit.mem_gibbsMeasures_of_tendsto_finiteVolumeLaw_of_isLocallyConstant
#print axioms FK.InfiniteVolume.InteriorWeakLimit.mem_dlrMeasures_of_tendsto_of_globalAtMostOne
#print axioms FK.InfiniteVolume.InteriorWeakLimit.mem_dlrMeasures_wired_of_tendsto_of_globalAtMostOne

-- Active-device DLR sandwiches and all weak-limit transport layers.
#print axioms FK.EnhancedTransport.lt_dlr_sandwich_of_active_devices_interior
#print axioms FK.EnhancedTransport.gt_dlr_sandwich_of_active_devices_interior
#print axioms FK.EnhancedTransport.cylinderDominates_of_isFKLimit_eventually_lower
#print axioms FK.EnhancedTransport.cylinderDominates_of_isFKLimit_eventually_upper
#print axioms FK.EnhancedTransport.stochasticallyDominates_of_isFKLimit_eventually_lower
#print axioms FK.EnhancedTransport.stochasticallyDominates_of_isFKLimit_eventually_upper
#print axioms FK.EnhancedTransport.fkLimit_lower_cutset_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.fkLimit_upper_cutset_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.fkLimit_upper_path_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.fkLimit_lower_path_comparison_of_rate_bound

-- Exact edge gadget, pivot transport, marginal, essentiality and packing.
#print axioms FK.AGGadget.activationPivotal_bondToActivation
#print axioms FK.AGGadget.edgePivotal_event_mul_le
#print axioms FK.AGGadget.sum_edgePivotal_event_mul_le
#print axioms FK.AGGadget.prod_boolLaw_map_or
#print axioms FK.AGGadget.jointLaw_map_paired
#print axioms FK.AGGadget.enhancedConfig_jointLaw
#print axioms FK.AGGadget.enhancedEvent_jointLaw
#print axioms FK.AGGadget.enhancedEssential_of_onDoubleRay
#print axioms FK.AGGadget.exists_boundedDistance_enhancedEssential
#print axioms FK.AGGadget.exists_lineGraphBoundedDistance_enhancedEssential

-- Special-family matroid dual certificates.
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.cycle_indep_iff
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.cycleDual_indep_iff
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.cycle_isBase_iff
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.cycleDual_isBase_iff
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.cycle_dual_cycleMatroid
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.graphicDualCertificate_cycle
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.graphicDualCertificate_parallel
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.graphicDualCertificate_oneEdgeLoopCycle
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.graphicDualCertificate_twoEdgeCycle

-- Finite cut/circuit interfaces.
#print axioms FK.Finite.LabelledMultigraph.not_spanning_compl_vertexCut
#print axioms FK.Finite.LabelledMultigraph.closed_of_mem_vertexCut_of_openComponentSaturated
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.exists_isCocircuit_subset_vertexCut
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.exists_faceDual_isCircuit_subset_vertexCut
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.exists_dualOpen_isCircuit_subset_vertexCut
#print axioms FK.Finite.LabelledMultigraph.openComponentSaturated_openVertexComponent
#print axioms FK.Finite.LabelledMultigraph.reachable_sdiff_singleton_of_cycleMatroid_isCircuit
#print axioms FK.Finite.PlaneMatroid.LabelledDualPair.exists_dualOpen_circuit_boundary_openComponent
