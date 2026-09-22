import AKM15SameGradedRestrictionCompatibility
import AKL5UniformAnnularSequence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualAnnularExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

include small in
/-- The actual full original equation set is stable under its proved
endpoint-changing restriction, with the new incoming datum reconstructed. -/
theorem restrictedOriginalEquationGraph
    (field : OriginalFiveBlockAmbient parameters lower length lowerPositive)
    (equation : field ∈ OriginalObservedEquationGraph parameters length compact lower lowerPositive
      (included.trans upperHalf) lengthPositive widthHalf widthLength state) :
    originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included field ∈
      OriginalObservedEquationGraph parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state := by
  obtain ⟨pair,actual,rfl⟩ := equation
  refine ⟨(originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
    (Grad.AnnularForwardDatum.originalFiveBlockObservation parameters lower length lowerPositive pair.1 pair.2),
    originalRetainedRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included pair.2), ?_, ?_⟩
  · exact originalEndpointDatum_equation parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
      widthHalf widthLength small pair.1 pair.2 actual
  · exact originalEndpointDatum_observation parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state pair.1 pair.2

/-- Only compactness on this FIXED collar uses the inverse BF6 coordinate
norm. The native retained estimate remains radius-uniform elsewhere. -/
theorem originalFiveBlock_fixedCollarBound
    (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : OriginalFiveBlockAmbient parameters lower length positive)
    (constant : ℝ)
    (estimate : originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive field.ofLp.1 ≤ constant) :
    ‖field‖ ≤ ‖(originalCoupledEquivalence parameters lower length positive bounded lengthPositive).symm.toContinuousLinearMap‖ * constant + ‖field.ofLp.2‖ := by
  let equivalence := originalCoupledEquivalence parameters lower length positive bounded lengthPositive
  have retained := equivalence.symm.toContinuousLinearMap.le_opNorm (equivalence field.ofLp.1)
  have exactRetained : ‖field.ofLp.1‖ ≤ ‖equivalence.symm.toContinuousLinearMap‖ * ‖equivalence field.ofLp.1‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using retained
  exact (Grad.AnnularHighGenerators.hilbertProduct_norm_le_add field).trans
    (add_le_add (exactRetained.trans (mul_le_mul_of_nonneg_left estimate (ContinuousLinearMap.opNorm_nonneg equivalence.symm.toContinuousLinearMap))) le_rfl)

end Grad.ActualAnnularExhaustion
