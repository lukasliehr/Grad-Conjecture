import AEM16LiteralHighCrossDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularOmegaGraph Grad.AnnularTiltedReference

theorem highCrossSlot_outside {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (field : AnnularBulk lower) (mode : ℤ × ℤ) (outside : ¬ 3 ≤ |mode.1|) :
    highBulkSlot lower slot field mode = 0 := by
  change radialMatrixUnit lower slot 0 (highBulkIntoFull lower field mode) = 0
  rw [highBulkIntoFull_low lower field mode outside, map_zero]

theorem highCrossSevenInput_outside (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) (mode : ℤ × ℤ) (outside : ¬ 3 ≤ |mode.1|) :
    highCrossSevenInput lower length positive lengthPositive field mode = 0 := by
  let decoded := bEnergyDecode lower length positive (crossHighW lower length positive lengthPositive field)
  change highBulkSlot lower (0 : Fin 7) (crossHighX lower length positive lengthPositive field) mode +
    highBulkSlot lower (1 : Fin 7) (highEnergyAngularRadius lower length positive decoded) mode +
    highBulkSlot lower (2 : Fin 7) ((length : ℂ) • highEnergyCell lower length positive decoded) mode +
    highBulkSlot lower (3 : Fin 7) (highEnergyRadius lower length positive decoded) mode = 0
  rw [highCrossSlot_outside lower 0 _ mode outside, highCrossSlot_outside lower 1 _ mode outside,
    highCrossSlot_outside lower 2 _ mode outside, highCrossSlot_outside lower 3 _ mode outside]
  simp only [add_zero]

theorem highCircular_crossLow_zero (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (row : Fin 3) (field : CrossHighSpace lower length positive lengthPositive) :
    lowFullRestriction lower (lowCircularRowAction parameters length lower positive bounded row
      (highCrossSevenInput lower length positive lengthPositive field)) = 0 := by
  apply lp.ext
  funext mode
  change lowCircularRowAction parameters length lower positive bounded row
    (highCrossSevenInput lower length positive lengthPositive field) mode.val = 0
  apply circularRow_zero_coefficient
  exact highCrossSevenInput_outside lower length positive lengthPositive field mode.val (by
    have low := mode.property
    omega)

theorem highCircular_firstOutput_zero (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : CrossHighSpace lower length positive lengthPositive) :
    lowFirstOutput parameters lower length (lowCircularRowAction parameters length lower positive bounded 0
      (highCrossSevenInput lower length positive lengthPositive field)) = 0 := by
  unfold lowFirstOutput lowOutputMap
  simp only [ContinuousLinearMap.comp_apply, highCircular_crossLow_zero, map_zero]

theorem highCircular_cellOutput_zero (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : CrossHighSpace lower length positive lengthPositive) :
    lowCellOutput lower length positive (lowCircularRowAction parameters length lower positive bounded 1
      (highCrossSevenInput lower length positive lengthPositive field)) = 0 := by
  unfold lowCellOutput lowOutputMap
  simp only [smul_apply, ContinuousLinearMap.comp_apply, highCircular_crossLow_zero, map_zero, smul_zero]

theorem highCircular_angularOutput_zero (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : CrossHighSpace lower length positive lengthPositive) :
    lowAngularOutput lower length positive (lowCircularRowAction parameters length lower positive bounded 2
      (highCrossSevenInput lower length positive lengthPositive field)) = 0 := by
  unfold lowAngularOutput lowOutputMap
  simp only [smul_apply, ContinuousLinearMap.comp_apply, highCircular_crossLow_zero, map_zero, smul_zero]

/-- BF18's actual low normalized source, with derivatives on the output
coefficients and the original a_m mu normalization. -/
def highToLowBulkCross (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) :
    CrossHighSpace lower length positive lengthPositive →L[ℂ] LowEnergyBulk lower :=
  (lowFirstOutput parameters lower length ∘L lowPhysicalRowAction parameters length compact lower positive bounded state 0 +
    lowCellOutput lower length positive ∘L lowPhysicalRowAction parameters length compact lower positive bounded state 1 +
    lowAngularOutput lower length positive ∘L lowPhysicalRowAction parameters length compact lower positive bounded state 2) ∘L
    highCrossSevenInput lower length positive lengthPositive

theorem highToLowBulkCross_error (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (field : CrossHighSpace lower length positive lengthPositive) :
    highToLowBulkCross parameters lower length compact lengthPositive positive bounded state field =
      lowFirstOutput parameters lower length (lowPhysicalRowErrorAction parameters length compact lower positive bounded state 0
        (highCrossSevenInput lower length positive lengthPositive field)) +
      lowCellOutput lower length positive (lowPhysicalRowErrorAction parameters length compact lower positive bounded state 1
        (highCrossSevenInput lower length positive lengthPositive field)) +
      lowAngularOutput lower length positive (lowPhysicalRowErrorAction parameters length compact lower positive bounded state 2
        (highCrossSevenInput lower length positive lengthPositive field)) := by
  simp only [highToLowBulkCross, ContinuousLinearMap.comp_apply, add_apply, lowPhysicalRowErrorAction_sub,
    sub_apply, map_sub, highCircular_firstOutput_zero, highCircular_cellOutput_zero, highCircular_angularOutput_zero, sub_zero]

end Grad.AnnularCrossMaps
