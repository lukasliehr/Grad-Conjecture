import BKC9PhysicalSevenSlotSupport

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- A full kernel with no angular displacement. Cell convolution remains
unrestricted. This is the exact support of the gauge mean matrix. -/
def AngularDiagonalKernel {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) : Prop :=
  ∀ shift frequency, shift.1 ≠ 0 → kernel.entry shift frequency = 0

theorem AngularDiagonalKernel.add {input output : ℕ} {parameters : PhaseParameters}
    {first second : FullTwoFrequencyKernel parameters input output}
    (hfirst : AngularDiagonalKernel first) (hsecond : AngularDiagonalKernel second) :
    AngularDiagonalKernel (fullKernelAdd first second) := by
  intro shift frequency nonzero
  rw [fullKernelAdd_entry, hfirst shift frequency nonzero,
    hsecond shift frequency nonzero, add_zero]

theorem AngularDiagonalKernel.neg {input output : ℕ} {parameters : PhaseParameters}
    {kernel : FullTwoFrequencyKernel parameters input output}
    (supported : AngularDiagonalKernel kernel) :
    AngularDiagonalKernel (fullKernelNeg kernel) := by
  intro shift frequency nonzero
  rw [fullKernelNeg_entry, supported shift frequency nonzero, neg_zero]

theorem AngularDiagonalKernel.comp {input middle output : ℕ}
    {parameters : PhaseParameters}
    {outer : FullTwoFrequencyKernel parameters middle output}
    {inner : FullTwoFrequencyKernel parameters input middle}
    (houter : AngularDiagonalKernel outer) (hinner : AngularDiagonalKernel inner) :
    AngularDiagonalKernel (fullKernelComposition outer inner) := by
  intro total frequency nonzero
  rw [fullKernelComposition_entry]
  have each (shift : ℤ × ℤ) :
      fullKernelCompositionTerm outer inner total shift frequency = 0 := by
    unfold fullKernelCompositionTerm
    by_cases angularZero : shift.1 = 0
    · have outerNonzero : (total - shift).1 ≠ 0 := by
        change total.1 - shift.1 ≠ 0
        simpa only [angularZero, sub_zero] using nonzero
      rw [houter (total - shift) _ outerNonzero]
      exact ContinuousLinearMap.zero_comp _
    · rw [hinner shift frequency angularZero]
      exact ContinuousLinearMap.comp_zero _
  change (∑' shift, fullKernelCompositionTerm outer inner total shift frequency) = 0
  simp only [each, tsum_zero]

theorem fullIdentityKernel_angularDiagonal (parameters : PhaseParameters) (dimension : ℕ) :
    AngularDiagonalKernel (fullIdentityKernel parameters dimension) := by
  intro shift frequency nonzero
  apply fullIdentityKernel_entry_ne_zero parameters dimension shift frequency
  intro equality
  exact nonzero (congrArg Prod.fst equality)

theorem AngularDiagonalKernel.power {dimension : ℕ} {parameters : PhaseParameters}
    {kernel : FullTwoFrequencyKernel parameters dimension dimension}
    (supported : AngularDiagonalKernel kernel) (exponent : ℕ) :
    AngularDiagonalKernel (fullKernelPower kernel exponent) := by
  induction exponent with
  | zero => exact supported
  | succ exponent ih => exact ih.comp supported

theorem AngularDiagonalKernel.neumannTail {dimension : ℕ}
    {parameters : PhaseParameters}
    {kernel : FullTwoFrequencyKernel parameters dimension dimension}
    (supported : AngularDiagonalKernel kernel)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low) (lowSmall : low < 1) :
    AngularDiagonalKernel (fullKernelNeumannTail parameters kernel low lowBound lowSmall) := by
  intro shift frequency nonzero
  rw [fullKernelNeumannTail_entry]
  simp only [fun exponent => supported.power exponent shift frequency nonzero, tsum_zero]

theorem AngularDiagonalKernel.negativeIdentityInverse {dimension : ℕ}
    {parameters : PhaseParameters}
    {kernel : FullTwoFrequencyKernel parameters dimension dimension}
    (supported : AngularDiagonalKernel kernel)
    (low : ℝ) (lowBound : fullKernelMoment parameters 0 kernel ≤ low) (lowSmall : low < 1) :
    AngularDiagonalKernel
      (fullKernelNegativeIdentityInverse parameters kernel low lowBound lowSmall) :=
  ((fullIdentityKernel_angularDiagonal parameters dimension).add
    (supported.neumannTail low lowBound lowSmall)).neg

theorem AngularDiagonalKernel.action_constant {input output : ℕ}
    {parameters : PhaseParameters} (angular cell : ℕ)
    {kernel : FullTwoFrequencyKernel parameters input output}
    (supported : AngularDiagonalKernel kernel)
    (field : NegativeTrace parameters angular cell input)
    (fieldSupported : IsAngularConstant parameters angular cell field) :
    IsAngularConstant parameters angular cell
      (fullNegativeKernelAction parameters angular cell kernel field) := by
  intro mode nonzero
  rw [← (fullNegativeKernelAction_coefficient_hasSum parameters angular cell kernel
    field mode).tsum_eq]
  have each (shift : ℤ × ℤ) :
      kernel.entry shift (twoFrequencyTranslation shift mode)
        (negativeTraceCoefficient parameters angular cell field
          (twoFrequencyTranslation shift mode)) = 0 := by
    by_cases angularZero : shift.1 = 0
    · have inputNonzero : (twoFrequencyTranslation shift mode).1 ≠ 0 := by
        simpa only [twoFrequencyTranslation_apply, angularZero, sub_zero] using nonzero
      rw [fieldSupported _ inputNonzero, map_zero]
    · rw [supported shift _ angularZero]
      rfl
  simp only [each, tsum_zero]

theorem constantMatrixKernel_action_constant {input output : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : NegativeTrace parameters angular cell input)
    (supported : IsAngularConstant parameters angular cell field) :
    IsAngularConstant parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (constantMatrixKernel parameters input output mapping) field) := by
  intro mode nonzero
  rw [constantMatrixKernel_action_coefficient, supported mode nonzero, map_zero]

end Grad.BoundaryKernelAction
