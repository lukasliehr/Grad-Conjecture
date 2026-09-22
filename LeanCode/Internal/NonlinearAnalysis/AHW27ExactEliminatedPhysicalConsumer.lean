import AHW26PhysicalErrorOneHighAndJets

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

/-- The actual first-row solution lies in the original retained sector. -/
theorem radialEliminatedXKernel_action_high (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) :
    IsHighAngularTrace (radialKernelParameters parameters r) angular cell
      (fullNegativeKernelAction _ angular cell (radialEliminatedXKernel parameters L compact state r) input) := by
  have equality := congrArg (fun kernel => fullNegativeKernelAction (radialKernelParameters parameters r) angular cell kernel input)
    (radialEliminatedXKernel_high_left parameters L compact state r)
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply] at equality
  rw [← equality]
  exact highAngularKernel_high _ angular cell _

/-- SAME original physical first-force row, without requiring a separate solution parameter. -/
theorem radialEliminatedXKernel_originalForce (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (positive : 0 < r.val) (angular cell : ℕ)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) :
    originalEightFirstForceEquation parameters L compact state r positive angular cell
      (fullNegativeKernelAction _ angular cell (radialEliminatedXKernel parameters L compact state r) input) input :=
  (originalEightFirstForceEquation_iff parameters L compact state r positive angular cell _
    (radialEliminatedXKernel_action_high parameters L compact state r angular cell input) input).mpr rfl

/-- Canonical completed bulk output coordinates match the exact first-row and flux kernels. -/
theorem radialEliminatedBulkKernel_action_coefficients (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (input : NegativeTrace (radialKernelParameters parameters r) angular cell 8) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters r) angular cell
      (fullNegativeKernelAction _ angular cell (radialEliminatedBulkKernel parameters L compact state r) input) mode =
    WithLp.toLp 2 ![
      negativeTraceCoefficient (radialKernelParameters parameters r) angular cell
        (fullNegativeKernelAction _ angular cell (radialEliminatedXKernel parameters L compact state r) input) mode 0,
      negativeTraceCoefficient (radialKernelParameters parameters r) angular cell
        (fullNegativeKernelAction _ angular cell (radialNormalizedCKernel parameters L compact state r)
          (fullNegativeKernelAction _ angular cell (radialEliminatedSevenKernel parameters L compact state r) input)) mode 0,
      negativeTraceCoefficient (radialKernelParameters parameters r) angular cell
        (fullNegativeKernelAction _ angular cell (radialNormalizedRVKernel parameters L compact state r)
          (fullNegativeKernelAction _ angular cell (radialEliminatedSevenKernel parameters L compact state r) input)) mode 0] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [radialEliminatedBulkKernel, radialEliminatedCKernel, radialEliminatedRVKernel,
      fullNegativeKernelAction_add, fullNegativeKernelAction_comp, negativeTraceCoefficient_add,
      coordinateInjectionKernel_action_coefficient]

end Grad.AnnularReconstruction

namespace Grad.AnnularKernelL2
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction

/-- Radius-uniform B8 bound on the actual completed BF error output (x,c,rV). -/
theorem eliminatedBulkCompletedError_B8 (parameters : PhaseParameters) (L compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
      (state : RetainedInverseState parameters L compact) (input : DivisionRow 8 lower),
      ‖eliminatedBulkErrorAction parameters L compact lower positive bounded state 1 input‖ ≤
        constant * state.val.errorBudget 1 * ‖input‖ := by
  refine ⟨eliminatedBulkErrorConstant parameters L compact 1,
    eliminatedBulkErrorConstant_nonnegative parameters L compact 1, ?_⟩
  exact fun lower positive bounded state input => eliminatedBulkErrorAction_bound parameters L compact lower positive bounded state 1 input

end Grad.AnnularKernelL2
