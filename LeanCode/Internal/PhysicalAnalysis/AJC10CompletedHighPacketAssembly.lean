import AJC9ExactSharedCrossSources

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularCurrentSolution
open Grad.AnnularPhysicalSolution Grad.AnnularKernelL2 Grad.AnnularReconstruction

theorem highRowProjection_modeMap (lower : ℝ)
    (family : (ℤ × ℤ) → RadialL2 1 lower →L[ℂ] RadialL2 1 lower)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bound : ∀ mode field, ‖family mode field‖ ≤ constant * ‖field‖)
    (field : DivisionRow 1 lower) :
    highRowProjection lower (complexLpTwoMap family constant nonnegative bound field) =
      complexLpTwoMap family constant nonnegative bound (highRowProjection lower field) := by
  apply lp.ext
  funext mode
  change highRowProjection lower (complexLpTwoMap family constant nonnegative bound field) mode =
    family mode (highRowProjection lower field mode)
  by_cases high : 3 ≤ |mode.1|
  · rw [highRowProjection_high lower _ ⟨mode, high⟩, highRowProjection_high lower field ⟨mode, high⟩]
    rfl
  · rw [highRowProjection_low lower _ mode high, highRowProjection_low lower field mode high, map_zero]

theorem highRowProjection_radius (lower : ℝ) (positive : 0 < lower) (field : DivisionRow 1 lower) :
    highRowProjection lower (radialRadiusRow lower positive field) =
      radialRadiusRow lower positive (highRowProjection lower field) :=
  highRowProjection_modeMap lower _ _ _ _ field

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)

/-- Actual completed x,c,rV evaluated on the same eliminated seven inputs. -/
theorem eliminatedBulkAction_sameSeven (input : DivisionRow 8 lower) :
    eliminatedBulkAction parameters L compact lower positive bounded state 0 input =
      bulkMatrixUnit lower (0 : Fin 3) 0 (eliminatedXAction parameters L compact lower positive bounded state 0 input) +
      bulkMatrixUnit lower (1 : Fin 3) 0 (normalizedCBulkAction parameters L compact lower positive bounded state 0
        (eliminatedSevenBulkAction parameters L compact lower positive bounded state 0 input)) +
      bulkMatrixUnit lower (2 : Fin 3) 0 (normalizedRVBulkAction parameters L compact lower positive bounded state 0
        (eliminatedSevenBulkAction parameters L compact lower positive bounded state 0 input)) := by
  rw [eliminatedBulkAction_assembled, eliminatedSevenBulkAction_assembled]
  rfl

omit bounded in
/-- The high output separates only its physical input and the direct
auxiliary rows; both are literal completed operators on original inputs. -/
theorem actualFullHighOutput_sameSeven (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : annularEnergySpace lower L positive) (known : HighKnownSourceBulk lower)
    (auxiliary : HighAuxiliarySourceBulk lower) :
    let input := fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, known)
    actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary =
      (bulkMatrixUnit lower (0 : Fin 3) 0 (eliminatedXAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input) +
      bulkMatrixUnit lower (1 : Fin 3) 0 (normalizedCBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input)) +
      bulkMatrixUnit lower (2 : Fin 3) 0 (normalizedRVBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
        (eliminatedSevenBulkAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0 input))) +
      (bulkMatrixUnit lower (1 : Fin 3) 0 (auxiliary 1) +
        bulkMatrixUnit lower (2 : Fin 3) 0 (auxiliary 2 - radialRadiusRow lower positive (auxiliary 0))) := by
  exact (actualFullHighOutput_one_packet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field known auxiliary).trans
    (congrArg (fun packet : DivisionRow 3 lower => packet + directKnownThreePacket lower positive auxiliary)
      (eliminatedBulkAction_sameSeven parameters L compact lower positive (lowerHalf.trans (by norm_num)) state
        (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, known))))

end Grad.AnnularStrongSolution
