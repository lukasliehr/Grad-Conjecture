import BCT15GenuinePhysicalBoundary

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

/-- AH16's full mean-free input sector, including the low nonzero angular
modes. Only the boundary output is projected to the high sector. -/
def meanFreeAngularSubmodule (parameters : PhaseParameters) (angular cell : ℕ) :
    Submodule ℂ (NegativeTrace parameters angular cell 1) where
  carrier := {field | IsAngularMeanFree parameters angular cell field}
  zero_mem' := by
    intro axial
    exact (negativeTraceCoefficientCLM parameters angular cell (0, axial)).map_zero
  add_mem' := by
    intro first second hfirst hsecond axial
    rw [negativeTraceCoefficient_add, hfirst axial, hsecond axial, add_zero]
  smul_mem' := by
    intro scalar field supported axial
    rw [negativeTraceCoefficient_smul, supported axial, smul_zero]

theorem meanFreeAngularSubmodule_closed (parameters : PhaseParameters) (angular cell : ℕ) :
    IsClosed (meanFreeAngularSubmodule parameters angular cell :
      Set (NegativeTrace parameters angular cell 1)) := by
  change IsClosed {field : NegativeTrace parameters angular cell 1 |
    ∀ axial : ℤ, negativeTraceCoefficient parameters angular cell field (0, axial) = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun axial =>
    (negativeTraceCoefficientCLM (dimension := 1) parameters angular cell (0, axial)).isClosed_ker

abbrev MeanFreeBoundaryPrimitive (parameters : PhaseParameters) (angular cell : ℕ) :=
  meanFreeAngularSubmodule parameters angular cell

instance meanFreeBoundaryPrimitive_complete (parameters : PhaseParameters) (angular cell : ℕ) :
    CompleteSpace (MeanFreeBoundaryPrimitive parameters angular cell) :=
  (meanFreeAngularSubmodule_closed parameters angular cell).completeSpace_coe

def meanFreeBoundaryPrimitiveTrace (parameters : PhaseParameters) (angular cell : ℕ)
    (field : MeanFreeBoundaryPrimitive parameters angular cell) :
    NegativeTrace parameters angular cell 1 :=
  fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1) field.val

theorem meanFreeBoundaryPrimitive_derivative (parameters : PhaseParameters) (angular cell : ℕ)
    (field : MeanFreeBoundaryPrimitive parameters angular cell) :
    IsAngularDerivative parameters angular cell
      (meanFreeBoundaryPrimitiveTrace parameters angular cell field) field.val :=
  angularInverseKernel_derivative parameters angular cell field.val field.property

theorem meanFreeBoundaryPrimitiveTrace_meanFree (parameters : PhaseParameters) (angular cell : ℕ)
    (field : MeanFreeBoundaryPrimitive parameters angular cell) :
    IsAngularMeanFree parameters angular cell
      (meanFreeBoundaryPrimitiveTrace parameters angular cell field) := by
  intro axial
  rw [meanFreeBoundaryPrimitiveTrace, angularInverseKernel,
    scalarModeDiagonalKernel_action_coefficient]
  simp [angularInverseMultiplier]

theorem meanFreeBoundaryPrimitive_norm (parameters : PhaseParameters) (angular cell : ℕ)
    (field : MeanFreeBoundaryPrimitive parameters angular cell) :
    ‖field‖ = ‖field.val‖ := rfl

theorem meanFreeBoundaryPrimitive_norm_sq (parameters : PhaseParameters) (angular cell : ℕ)
    (field : MeanFreeBoundaryPrimitive parameters angular cell) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      negativeTraceWeightSq parameters angular cell mode * |(mode.1 : ℝ)| ^ 2 *
        ‖negativeTraceCoefficient parameters angular cell
          (meanFreeBoundaryPrimitiveTrace parameters angular cell field) mode‖ ^ 2 := by
  rw [meanFreeBoundaryPrimitive_norm, negativeTrace_norm_sq]
  apply tsum_congr
  intro mode
  rw [meanFreeBoundaryPrimitive_derivative parameters angular cell field mode,
    norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, mul_pow]
  ring

theorem meanFreeBoundaryPrimitiveTrace_injective (parameters : PhaseParameters) (angular cell : ℕ) :
    Function.Injective (meanFreeBoundaryPrimitiveTrace parameters angular cell) := by
  intro first second equality
  apply Subtype.ext
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [meanFreeBoundaryPrimitive_derivative parameters angular cell first mode,
    meanFreeBoundaryPrimitive_derivative parameters angular cell second mode, equality]

end Grad.ActualBoundaryPrimitives
