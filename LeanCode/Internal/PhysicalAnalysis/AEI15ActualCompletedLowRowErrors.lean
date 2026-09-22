import AEI14ActualCurrentLowPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

def lowPhysicalRowAction (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact) (row : Fin 3) :
    DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)

def lowCircularRowAction (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (row : Fin 3) : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded (lowCircularRowKernel parameters length row)
    (lowCircularRowKernel_regular parameters length row)

/-- The actual current-minus-circular operator, on the same stored radial L2. -/
def lowPhysicalRowErrorAction (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact) (row : Fin 3) :
    DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded
    (fun radius => fullKernelSub (lowPhysicalRowKernel parameters length compact state row radius) (lowCircularRowKernel parameters length row radius))
    ((lowPhysicalRowKernel_regular parameters length compact state row).sub (lowCircularRowKernel_regular parameters length row))

theorem lowPhysicalRowErrorAction_sub (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact) (row : Fin 3) :
    lowPhysicalRowErrorAction parameters length compact lower positive bounded state row =
      lowPhysicalRowAction parameters length compact lower positive bounded state row -
        lowCircularRowAction parameters length lower positive bounded row :=
  regularRadialBulkAction_sub parameters 0 lower positive bounded
    (lowPhysicalRowKernel parameters length compact state row) (lowPhysicalRowKernel_regular parameters length compact state row)
    (lowCircularRowKernel parameters length row) (lowCircularRowKernel_regular parameters length row)

theorem lowPhysicalRowErrorAction_bound (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)
    (row : Fin 3) (field : DivisionRow 7 lower) :
    ‖lowPhysicalRowErrorAction parameters length compact lower positive bounded state row field‖ ≤
      lowPhysicalRowErrorConstant parameters length compact row * state.val.errorBudget 0 * ‖field‖ := by
  let delta := fun radius => fullKernelSub (lowPhysicalRowKernel parameters length compact state row radius)
    (lowCircularRowKernel parameters length row radius)
  let regular := (lowPhysicalRowKernel_regular parameters length compact state row).sub (lowCircularRowKernel_regular parameters length row)
  have moment : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      fullKernelMoment (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0
        (delta (collarRadius lower positive bounded radius)) ≤
      lowPhysicalRowErrorConstant parameters length compact row * state.val.errorBudget 0 :=
    Filter.Eventually.of_forall (fun radius => lowPhysicalRowError_moment parameters length compact state row (collarRadius lower positive bounded radius))
  have represented := regularRadialBulkAction_eq_completed parameters 0 lower positive bounded delta regular
    (regularRadialBulk_measurable parameters lower positive bounded delta regular)
    (lowPhysicalRowErrorConstant parameters length compact row * state.val.errorBudget 0) moment
  change ‖regularRadialBulkAction parameters 0 lower positive bounded delta regular field‖ ≤ _
  rw [represented]
  exact completedBulkKernel_bound _ _ _ _ _ _ _ _ _ field

theorem lowPhysicalRowErrorAction_B8 (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)
    (row : Fin 3) (field : DivisionRow 7 lower) :
    ‖lowPhysicalRowErrorAction parameters length compact lower positive bounded state row field‖ ≤
      lowPhysicalRowErrorConstant parameters length compact row *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  apply (lowPhysicalRowErrorAction_bound parameters length compact lower positive bounded state row field).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
  exact mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon
    (show 0 + 7 ≤ 8 by omega)) (lowPhysicalRowErrorConstant_nonnegative parameters length compact row)

end Grad.AnnularCurrentLow
