import AIE5CompleteGraphEnergyConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularCurrentSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularUniformBoundary

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

theorem actualFullHighOutput_bound
    (field : annularEnergySpace lower L positive) (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower) :
    ‖actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary‖ ≤
      eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * (4 + 2 * |L|) * ‖field‖ +
        4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖known‖ + 3 * ‖auxiliary‖ := by
  have positiveCoefficient := mul_nonneg (eliminatedBulkConstant_nonnegative parameters L compact 0)
    (state.val.val.size_nonnegative 0)
  have input := highEightEnergyPacket_bound parameters lower L positive lengthPositive widthHalf widthLength field
  have action := eliminatedBulkAction_bound parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
    (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field)
  have knownBound := actualHighKnownBulkOutput_bound parameters L compact lower positive lowerHalf state known auxiliary
  apply (norm_add_le _ _).trans
  exact (add_le_add (action.trans (mul_le_mul_of_nonneg_left input positiveCoefficient)) knownBound).trans_eq (by ring)

/-- The full recovered physical packet attached to the same actual current
solution has a uniform bound in exactly the original BF2 source quantities. -/
theorem graphDataEnergySolution_fullOutput_bound
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)
    (data : ActualHighGraphKnownData parameters lower 0 0) :
    ‖actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
        data.weighted data.auxiliary‖ ≤
      eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * (4 + 2 * |L|) *
        (32 * data.functionalSize parameters L compact lower state 0 0 +
          322 * uniformInnerLiftConstant L * ‖data.innerValue‖) +
      4 * eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * ‖data.weighted‖ + 3 * ‖data.auxiliary‖ := by
  have output := actualFullHighOutput_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    data.weighted data.auxiliary
  have energy := graphDataEnergySolution_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have coefficient : 0 ≤ eliminatedBulkConstant parameters L compact 0 * state.val.val.size 0 * (4 + 2 * |L|) :=
    mul_nonneg (mul_nonneg (eliminatedBulkConstant_nonnegative parameters L compact 0) (state.val.val.size_nonnegative 0)) (by positivity)
  exact output.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left energy coefficient) le_rfl) le_rfl)

end Grad.AnnularCurrentSolution
