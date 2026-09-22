import BKC4ActualPerturbationSupport

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Ledger

theorem diagonalThreeMap_apply (first second third : ℂ)
    (value : ComplexEuclidean 3) :
    diagonalThreeMap first second third value =
      WithLp.toLp 2 ![first * value 0, second * value 1, third * value 2] := by
  apply PiLp.ext
  intro coordinate
  change first * (value 0 * (if coordinate = 0 then 1 else 0)) +
      second * (value 1 * (if coordinate = 1 then 1 else 0)) +
      third * (value 2 * (if coordinate = 2 then 1 else 0)) =
    ![first * value 0, second * value 1, third * value 2] coordinate
  fin_cases coordinate <;> simp

theorem diagonalThreeKernel_action_support
    (parameters : PhaseParameters) (angular cell : ℕ) (first second third : ℂ)
    (field : NegativeTrace parameters angular cell 3)
    (supported : EncodedSupport parameters angular cell field) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (constantMatrixKernel parameters 3 3 (diagonalThreeMap first second third))
        field) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mode nonzero
    rw [constantMatrixKernel_action_coefficient, diagonalThreeMap_apply]
    change first * negativeTraceCoefficient parameters angular cell field mode 0 = 0
    rw [supported.1 mode nonzero, mul_zero]
  · intro axial
    rw [constantMatrixKernel_action_coefficient, diagonalThreeMap_apply]
    change second * negativeTraceCoefficient parameters angular cell field (0, axial) 1 = 0
    rw [supported.2.1 axial, mul_zero]
  · intro axial
    rw [constantMatrixKernel_action_coefficient, diagonalThreeMap_apply]
    change third * negativeTraceCoefficient parameters angular cell field (0, axial) 2 = 0
    rw [supported.2.2 axial, mul_zero]

theorem encodedD0InverseKernel_action_support
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 3)
    (supported : EncodedSupport parameters angular cell field) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (encodedD0InverseKernel parameters) field) :=
  diagonalThreeKernel_action_support parameters angular cell _ _ _ field supported

/-- An already constructed right inverse preserves every additive support
condition when the perturbation has its entire range in that support.
The equation itself suffices; no convergence or closed-subspace premise is
introduced for the Neumann inverse. -/
theorem fullPositiveIdentityInverse_action_support {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (support : NegativeTrace parameters angular cell dimension → Prop)
    (subtract : ∀ {first second}, support first → support second → support (first - second))
    (perturbation inverse : FullTwoFrequencyKernel parameters dimension dimension)
    (right : fullKernelComposition
      (fullKernelAdd (fullIdentityKernel parameters dimension) perturbation) inverse =
        fullIdentityKernel parameters dimension)
    (range : ∀ field, support
      (fullNegativeKernelAction parameters angular cell perturbation field))
    (field : NegativeTrace parameters angular cell dimension)
    (supported : support field) :
    support (fullNegativeKernelAction parameters angular cell inverse field) := by
  have equation := congrArg
    (fun kernel => fullNegativeKernelAction parameters angular cell kernel field) right
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, fullNegativeKernelAction_identity,
    ContinuousLinearMap.id_apply] at equation
  have rearranged := eq_sub_of_add_eq equation
  rw [rearranged]
  exact subtract supported (range _)

end Grad.BoundaryKernelAction
