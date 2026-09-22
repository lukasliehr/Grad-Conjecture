import AEM13ExactHighOutputRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2

/-- The completed circular row preserves exact Fourier support. -/
theorem circularRow_zero_coefficient (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (row : Fin 3) (field : DivisionRow 7 lower)
    (mode : ℤ × ℤ) (zero : field mode = 0) :
    lowCircularRowAction parameters length lower positive bounded row field mode = 0 := by
  apply Lp.ext
  filter_upwards [lowCircularRowAction_ae parameters length lower positive bounded row field,
    Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1)),
    Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))] with radius actual zeroInput zeroOutput
  rw [actual mode, zero, zeroInput, zeroOutput]
  simp only [Pi.zero_apply, map_zero]

theorem lowCircular_crossHigh_zero (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (row : Fin 3) (field : LowEnergyBulk lower) :
    crossHighRestriction lower (lowCircularRowAction parameters length lower positive bounded row
      (lowNormalizedSevenInput parameters lower length lengthPositive positive field)) = 0 := by
  apply lp.ext
  funext mode
  change lowCircularRowAction parameters length lower positive bounded row
    (lowNormalizedSevenInput parameters lower length lengthPositive positive field) mode.val = 0
  apply circularRow_zero_coefficient
  exact lowNormalizedSevenInput_outside parameters lower length lengthPositive positive field mode.val (by
    have high := mode.property
    omega)

theorem lowPhysical_crossHigh_error (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (row : Fin 3) (field : LowEnergyBulk lower) :
    crossHighRestriction lower (lowPhysicalRowAction parameters length compact lower positive bounded state row
      (lowNormalizedSevenInput parameters lower length lengthPositive positive field)) =
    crossHighRestriction lower (lowPhysicalRowErrorAction parameters length compact lower positive bounded state row
      (lowNormalizedSevenInput parameters lower length lengthPositive positive field)) := by
  rw [lowPhysicalRowErrorAction_sub, sub_apply, map_sub, lowCircular_crossHigh_zero, sub_zero]

end Grad.AnnularCrossMaps
