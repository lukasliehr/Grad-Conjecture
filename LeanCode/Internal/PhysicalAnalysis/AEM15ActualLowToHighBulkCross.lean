import AEM14CircularCrossSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Allocation

/-- The three literal BF16 bulk entries are Qj, Qc, and rQV. -/
def lowToHighBulkCross (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (row : Fin 3) :
    lowEnergyGraph lower length positive →L[ℂ] AnnularBulk lower :=
  crossHighRestriction lower ∘L lowPhysicalRowAction parameters length compact lower positive bounded state row ∘L
    lowNormalizedSevenInput parameters lower length lengthPositive positive ∘L lowStoredCoordinate lower length positive 0

theorem lowToHighBulkCross_original (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (row : Fin 3)
    (field : lowEnergyGraph lower length positive) (mode : HighAnnularMode) :
    lowToHighBulkCross parameters lower length compact lengthPositive positive bounded state row field mode =
      lowPhysicalRowAction parameters length compact lower positive bounded state row
        (lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0)) mode.val := rfl

theorem lowToHighBulkCross_B8 (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (row : Fin 3)
    (field : lowEnergyGraph lower length positive) :
    ‖lowToHighBulkCross parameters lower length compact lengthPositive positive bounded state row field‖ ≤
      (lowPhysicalRowErrorConstant parameters length compact row * (7 + 2 * length)) *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  change ‖crossHighRestriction lower (lowPhysicalRowAction parameters length compact lower positive bounded state row
    (lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0)))‖ ≤ _
  rw [lowPhysical_crossHigh_error]
  apply (crossHighRestrictionValue_bound lower _).trans
  apply (lowPhysicalRowErrorAction_B8 parameters length compact lower positive bounded state row _).trans
  have inputBound := (lowNormalizedSevenInput_bound parameters lower length lengthPositive positive (field.val 0)).trans
    (mul_le_mul_of_nonneg_left (lowStoredCoordinate_bound lower length positive 0 field) (by linarith))
  have constant := mul_nonneg (lowPhysicalRowErrorConstant_nonnegative parameters length compact row)
    (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8)
  exact (mul_le_mul_of_nonneg_left inputBound constant).trans_eq (by ring)

/-- Same completed current rows as the low inverse, now read in the high
output sector and decoded by the original rho physical weight. -/
theorem lowToHighBulkCross_physical (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (row : Fin 3)
    (field : lowEnergyGraph lower length positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ) •
        lowOriginalCurrentRow parameters length compact lower lengthPositive positive bounded state field row radius mode.val =
      lowToHighBulkCross parameters lower length compact lengthPositive positive bounded.le state row field mode radius := by
  exact Filter.Eventually.of_forall (fun radius mode =>
    lowOriginalCurrentRow_encode parameters length compact lower lengthPositive positive bounded state field row radius mode.val)

end Grad.AnnularCrossMaps
