import BKC13ActualDecodedRotation

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualCurrentPrimitives

/-- The exact full two-frequency convolution product rule. Both output
series are already absolutely convergent in the original trace carrier. -/
theorem fullNegativeKernelAction_derivative {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (kernel rotated : FullTwoFrequencyKernel parameters input output)
    (rotatedEntry : ∀ shift frequency,
      rotated.entry shift frequency = (Complex.I * (shift.1 : ℂ)) •
        kernel.entry shift frequency)
    (field derivative : NegativeTrace parameters angular cell input)
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell kernel field)
      (fullNegativeKernelAction parameters angular cell rotated field +
        fullNegativeKernelAction parameters angular cell kernel derivative) := by
  intro mode
  rw [negativeTraceCoefficient_add]
  have left :=
    (fullNegativeKernelAction_coefficient_hasSum parameters angular cell rotated field mode).add
      (fullNegativeKernelAction_coefficient_hasSum parameters angular cell kernel derivative mode)
  have right :=
    (fullNegativeKernelAction_coefficient_hasSum parameters angular cell kernel field mode).const_smul
      (Complex.I * (mode.1 : ℂ))
  apply left.unique
  convert right using 1
  funext shift
  rw [rotatedEntry, smul_apply, differentiated, map_smul, ← add_smul]
  congr 1
  simp only [twoFrequencyTranslation_apply, Int.cast_sub]
  ring

/-- Multiplication by the literal angular derivative of a coefficient row
is the displacement multiplier of its full convolution kernel. -/
theorem boundaryRowMultiplicationKernel_rotated_entry
    (parameters : PhaseParameters) (dimension : ℕ)
    (coefficient : Fin dimension → ℤ × ℤ → ℂ)
    (moments : ∀ component moment,
      Summable (productMoment parameters moment 1 (coefficient component)))
    (rotatedMoments : ∀ component moment,
      Summable (productMoment parameters moment 1
        (angularCoefficientSequence (coefficient component))))
    (shift frequency : ℤ × ℤ) :
    (boundaryRowMultiplicationKernel parameters dimension
      (fun component => angularCoefficientSequence (coefficient component)) rotatedMoments).entry
        shift frequency =
      (Complex.I * (shift.1 : ℂ)) •
        (boundaryRowMultiplicationKernel parameters dimension coefficient moments).entry
          shift frequency := by
  apply ContinuousLinearMap.ext
  intro value
  rw [boundaryRowMultiplicationKernel_entry_apply, smul_apply,
    boundaryRowMultiplicationKernel_entry_apply, smul_smul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  unfold angularCoefficientSequence
  ring

/-- The literal row product rule, with the R row constructed from the same
coefficient family rather than provided as an additional physical premise. -/
theorem boundaryRowMultiplicationKernel_derivative
    (parameters : PhaseParameters) (angular cell dimension : ℕ)
    (coefficient : Fin dimension → ℤ × ℤ → ℂ)
    (moments : ∀ component moment,
      Summable (productMoment parameters moment 1 (coefficient component)))
    (rotatedMoments : ∀ component moment,
      Summable (productMoment parameters moment 1
        (angularCoefficientSequence (coefficient component))))
    (field derivative : NegativeTrace parameters angular cell dimension)
    (differentiated : IsAngularDerivative parameters angular cell field derivative) :
    IsAngularDerivative parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (boundaryRowMultiplicationKernel parameters dimension coefficient moments) field)
      (fullNegativeKernelAction parameters angular cell
        (boundaryRowMultiplicationKernel parameters dimension
          (fun component => angularCoefficientSequence (coefficient component)) rotatedMoments) field +
        fullNegativeKernelAction parameters angular cell
          (boundaryRowMultiplicationKernel parameters dimension coefficient moments) derivative) := by
  apply fullNegativeKernelAction_derivative parameters angular cell _ _
    _ field derivative differentiated
  exact boundaryRowMultiplicationKernel_rotated_entry parameters dimension
    coefficient moments rotatedMoments

end Grad.BoundaryKernelAction
