import BKC28DerivativePrimitive

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

theorem actualSigmaBoundaryKernel_derivative
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (angular cell : ℕ) (input derivative : NegativeTrace parameters angular cell 3)
    (differentiated : IsAngularDerivative parameters angular cell input derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualSigmaBoundaryKernel parameters L rho epsilon field low) input)
      (fullNegativeKernelAction parameters angular cell
        (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field low) input +
       fullNegativeKernelAction parameters angular cell
        (actualSigmaBoundaryKernel parameters L rho epsilon field low) derivative) :=
  boundaryRowMultiplicationKernel_derivative parameters angular cell 3 _ _ _
    input derivative differentiated

theorem actualSigmaComponentBoundaryKernel_derivative
    (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (angular cell : ℕ)
    (input derivative : NegativeTrace parameters angular cell 1)
    (differentiated : IsAngularDerivative parameters angular cell input derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualSigmaComponentBoundaryKernel parameters L rho epsilon field low component) input)
      (fullNegativeKernelAction parameters angular cell
        (actualRotatedSigmaComponentBoundaryKernel parameters L rho epsilon field low component) input +
       fullNegativeKernelAction parameters angular cell
        (actualSigmaComponentBoundaryKernel parameters L rho epsilon field low component) derivative) := by
  apply fullNegativeKernelAction_derivative parameters angular cell _ _ _ input derivative differentiated
  intro shift frequency
  unfold actualRotatedSigmaComponentBoundaryKernel actualSigmaComponentBoundaryKernel
  rw [boundaryScalarMultiplicationKernel_entry, boundaryScalarMultiplicationKernel_entry]
  unfold actualRotatedSigmaBoundaryCoefficients angularCoefficientSequence
  rw [smul_smul]

theorem encodedRotationKernel_first_coefficient
    (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 3) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
      (fullNegativeKernelAction parameters angular cell (encodedRotationKernel parameters) input)
      mode 0 = 0 := by
  simp only [encodedRotationKernel, fullNegativeKernelAction_add, negativeTraceCoefficient_add,
    PiLp.add_apply, angularInverseComponentKernel, angularMeanFreeComponentKernel,
    componentModeKernel_action_coefficient]
  simp [Fin.ext_iff]

variable (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compactRadius : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 7 ≤
      actualEncodedFirstLowRadius parameters L compactRadius)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius)
    (deltaSmall : |delta| ≤ compactRadius)
    (parameterSmall : |parameter| ≤ compactRadius)
    (angular cell : ℕ)

theorem actualUnknownVKernel_first
    (input : NegativeTrace parameters angular cell 1) :
    fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 0)
      (fullNegativeKernelAction parameters angular cell
        (actualUnknownVKernel parameters L rho alpha delta parameter epsilon compactRadius
          field small compactNonnegative alphaSmall deltaSmall parameterSmall) input) = input := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro coordinate
  have unique : coordinate = 0 := Fin.eq_zero coordinate
  subst coordinate
  rw [coordinateProjectionKernel_action_coefficient]
  unfold actualUnknownVKernel
  rw [fullNegativeKernelAction_add, negativeTraceCoefficient_add]
  simp only [PiLp.add_apply, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    encodedRotationKernel_first_coefficient, firstCoordinateInjectionKernel,
    coordinateInjectionKernel_action_coefficient, ite_true, zero_add]

theorem actualKnownRAStarKernel_first
    (input : SevenSlotTrace parameters angular cell) :
    fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 0)
      (fullNegativeKernelAction parameters angular cell
        (actualKnownRAStarKernel parameters L rho alpha delta parameter epsilon compactRadius
          field small compactNonnegative alphaSmall deltaSmall parameterSmall)
        (sevenSlotFlatten parameters angular cell input)) = 0 := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro coordinate
  have unique : coordinate = 0 := Fin.eq_zero coordinate
  subst coordinate
  rw [coordinateProjectionKernel_action_coefficient]
  unfold actualKnownRAStarKernel actualKnownRotatedQStarKernel
  rw [fullNegativeKernelAction_add, negativeTraceCoefficient_add]
  simp only [PiLp.add_apply, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    encodedRotationKernel_first_coefficient, secondCoordinateInjectionKernel,
    coordinateInjectionKernel_action_coefficient, zero_add]
  simp [negativeTraceCoefficient]

end Grad.BoundaryKernelAction
