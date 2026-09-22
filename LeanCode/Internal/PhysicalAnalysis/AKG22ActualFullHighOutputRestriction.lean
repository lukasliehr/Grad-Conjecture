import AKG21CorrectedHighKnownDataRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularVariational Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularCurrentSolution

/-- Restriction of the complete direct (g,c,rV) auxiliary tuple. -/
def auxiliaryRowsRestriction (lower upper : ℝ) (included : lower ≤ upper)
    (source : HighAuxiliarySourceBulk lower) : HighAuxiliarySourceBulk upper :=
  WithLp.toLp 2 (fun slot => originalBulkRestriction 1 lower upper included (source slot))

theorem directKnownThreePacket_restriction (lower upper : ℝ) (included : lower ≤ upper)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (source : HighAuxiliarySourceBulk lower) :
    originalBulkRestriction 3 lower upper included (directKnownThreePacket lower lowerPositive source) =
      directKnownThreePacket upper upperPositive (auxiliaryRowsRestriction lower upper included source) := by
  change originalBulkRestriction 3 lower upper included
    (bulkMatrixUnit lower (1 : Fin 3) 0 (source 1) +
      bulkMatrixUnit lower (2 : Fin 3) 0 (source 2 - radialRadiusRow lower lowerPositive (source 0))) = _
  rw [map_add,bulkMatrixUnit_restriction,bulkMatrixUnit_restriction,map_sub,originalBulkRestriction_radius lower upper lowerPositive upperPositive included]
  rfl

/-- Locality of the SAME actual full high output, including the retained
elimination and all direct known forcing. -/
theorem actualFullHighOutput_restriction (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact) (field : annularEnergySpace lower length lowerPositive)
    (known : HighKnownSourceBulk lower) (auxiliary : HighAuxiliarySourceBulk lower) :
    originalBulkRestriction 3 lower upper included
      (actualFullHighOutput parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive widthHalf widthLength state field known auxiliary) =
    actualFullHighOutput parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field)
      (knownRowsRestriction lower upper included known) (auxiliaryRowsRestriction lower upper included auxiliary) := by
  have eliminated := originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive
    (upperHalf.trans (by norm_num)) (radialEliminatedBulkKernel parameters length compact state)
    (radialEliminatedBulkKernel_regular parameters length compact state)
    (fullHighEightPacket parameters lower length lowerPositive lengthPositive widthHalf widthLength (field,known))
  rw [actualFullHighOutput_one_packet,actualFullHighOutput_one_packet,map_add,
    eliminatedBulkAction_eq_regular,eliminatedBulkAction_eq_regular,eliminated,directKnownThreePacket_restriction,
    fullHighEightPacket_restriction lower upper length lowerPositive upperPositive included parameters
      (upperHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength]

theorem strongCorrectedHighData_auxiliary_restriction (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0)
    (target : StrongDataCarrier parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0)
    (sameG : (strongToLow parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0 target).ofLp.1.ofLp.2 =
      originalBulkRestriction 1 lower upper included
        (strongToLow parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)
    (field : lowEnergyGraph lower length lowerPositive) :
    (strongCorrectedHighData parameters length compact upper upperPositive upperHalf lengthPositive state target
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) field)).auxiliary =
    auxiliaryRowsRestriction lower upper included
      (strongCorrectedHighData parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).auxiliary := by
  have packet := lowNormalizedSevenInput_restriction parameters lower upper length lowerPositive upperPositive
    (upperHalf.trans_lt (by norm_num)) lengthPositive included field
  have sameRow (slot : Fin 3) := (originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive
    (upperHalf.trans (by norm_num)) (lowPhysicalRowKernel parameters length compact state slot)
    (lowPhysicalRowKernel_regular parameters length compact state slot)
    (lowNormalizedSevenInput parameters lower length lengthPositive lowerPositive (field.val 0))).trans
      (congrArg (lowPhysicalRowAction parameters length compact upper upperPositive (upperHalf.trans (by norm_num)) state slot) packet)
  apply PiLp.ext
  intro slot
  change _ = originalBulkRestriction 1 lower upper included
    ((strongCorrectedHighData parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).auxiliary slot)
  fin_cases slot
  · exact (strongCorrectedHighData_g parameters length compact upper upperPositive upperHalf lengthPositive state target _).trans
      ((congrArg (highRowProjection upper) sameG).trans
        ((highRowProjection_restriction lower upper included _).symm.trans
          (congrArg (originalBulkRestriction 1 lower upper included)
            (strongCorrectedHighData_g parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).symm)))
  · have projected := (highRowProjection_restriction lower upper included _).trans (congrArg (highRowProjection upper) (sameRow 1))
    exact (strongCorrectedHighData_c parameters length compact upper upperPositive upperHalf lengthPositive state target _).trans
      (projected.symm.trans (congrArg (originalBulkRestriction 1 lower upper included)
        (strongCorrectedHighData_c parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).symm))
  · have projected := (highRowProjection_restriction lower upper included _).trans (congrArg (highRowProjection upper) (sameRow 2))
    exact (strongCorrectedHighData_v parameters length compact upper upperPositive upperHalf lengthPositive state target _).trans
      (projected.symm.trans (congrArg (originalBulkRestriction 1 lower upper included)
        (strongCorrectedHighData_v parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).symm))

end Grad.AnnularRestriction
