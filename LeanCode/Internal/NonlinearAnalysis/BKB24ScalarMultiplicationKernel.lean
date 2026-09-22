import BKB23NeumannInverseBounds
import SCC25BalancedCellProduct

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra

/-- The exact boundary phase cost is the physical radius-one coefficient
envelope, up to the fixed AH17 half-order constant. -/
theorem boundaryCoefficientPhaseCost_productMoment (parameters : PhaseParameters)
    (moment : ℕ) (coefficient : ℤ × ℤ → ℂ) (shift : ℤ × ℤ) :
    boundaryCoefficientPhaseCost parameters shift *
        annularFrequency shift.1 shift.2 ^ moment * ‖coefficient shift‖ =
      Real.exp (parameters.sigma0 + parameters.gamma) *
        productMoment parameters moment 1 coefficient shift := by
  simp only [boundaryCoefficientPhaseCost, phaseWeight, phaseWidth,
    productMoment, coefficientRadialEnvelope, mul_one]
  ring

def scalarMultiplicationEntry (dimension : ℕ) (coefficient : ℤ × ℤ → ℂ)
    (shift _input : ℤ × ℤ) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  coefficient shift • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)

theorem scalarMultiplicationEntry_norm_le (dimension : ℕ)
    (coefficient : ℤ × ℤ → ℂ) (shift input : ℤ × ℤ) :
    ‖scalarMultiplicationEntry dimension coefficient shift input‖ ≤
      ‖coefficient shift‖ := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ)
        (E := ComplexEuclidean dimension))
      (norm_nonneg (coefficient shift))

/-- A scalar Fourier coefficient family gives a genuine full AE7
multiplication kernel.  Its entries are independent of the input mode, while
the stored envelope remains the literal supremum required by AE20. -/
def boundaryScalarMultiplicationKernel (parameters : PhaseParameters)
    (dimension : ℕ) (coefficient : ℤ × ℤ → ℂ)
    (moments : ∀ moment : ℕ,
      Summable (productMoment parameters moment 1 coefficient)) :
    FullTwoFrequencyKernel parameters dimension dimension :=
  fullKernelOfEntries parameters
    (scalarMultiplicationEntry dimension coefficient)
    (fun shift => ‖coefficient shift‖)
    (scalarMultiplicationEntry_norm_le dimension coefficient)
    (fun moment => by
      apply ((moments moment).mul_left
        (Real.exp (parameters.sigma0 + parameters.gamma))).congr
      intro shift
      exact (boundaryCoefficientPhaseCost_productMoment
        parameters moment coefficient shift).symm)

@[simp] theorem boundaryScalarMultiplicationKernel_entry
    (parameters : PhaseParameters) (dimension : ℕ)
    (coefficient : ℤ × ℤ → ℂ)
    (moments : ∀ moment : ℕ,
      Summable (productMoment parameters moment 1 coefficient))
    (shift input : ℤ × ℤ) :
    (boundaryScalarMultiplicationKernel parameters dimension coefficient moments).entry
        shift input =
      coefficient shift • ContinuousLinearMap.id ℂ
        (ComplexEuclidean dimension) := rfl

theorem boundaryScalarMultiplicationKernel_entry_apply
    (parameters : PhaseParameters) (dimension : ℕ)
    (coefficient : ℤ × ℤ → ℂ)
    (moments : ∀ moment : ℕ,
      Summable (productMoment parameters moment 1 coefficient))
    (shift input : ℤ × ℤ) (value : ComplexEuclidean dimension) :
    (boundaryScalarMultiplicationKernel parameters dimension coefficient moments).entry
        shift input value = coefficient shift • value := by
  rw [boundaryScalarMultiplicationKernel_entry]
  simp

theorem boundaryScalarMultiplicationKernel_entryNorm_le
    (parameters : PhaseParameters) (dimension : ℕ)
    (coefficient : ℤ × ℤ → ℂ)
    (moments : ∀ moment : ℕ,
      Summable (productMoment parameters moment 1 coefficient))
    (shift : ℤ × ℤ) :
    (boundaryScalarMultiplicationKernel parameters dimension coefficient moments).entryNorm
        shift ≤ ‖coefficient shift‖ :=
  fullKernelOfEntries_entryNorm_le parameters
    (scalarMultiplicationEntry dimension coefficient)
    (fun shift => ‖coefficient shift‖)
    (scalarMultiplicationEntry_norm_le dimension coefficient)
    (fun moment => by
      apply ((moments moment).mul_left
        (Real.exp (parameters.sigma0 + parameters.gamma))).congr
      intro current
      exact (boundaryCoefficientPhaseCost_productMoment
        parameters moment coefficient current).symm)
    shift

theorem boundaryScalarMultiplicationKernel_moment_le
    (parameters : PhaseParameters) (dimension moment : ℕ)
    (coefficient : ℤ × ℤ → ℂ)
    (moments : ∀ order : ℕ,
      Summable (productMoment parameters order 1 coefficient)) :
    fullKernelMoment parameters moment
        (boundaryScalarMultiplicationKernel parameters dimension coefficient moments) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        ∑' shift, productMoment parameters moment 1 coefficient shift := by
  unfold fullKernelMoment
  have leftSummable :=
    (boundaryScalarMultiplicationKernel parameters dimension coefficient moments).moments
      moment
  have rightSummable := (moments moment).mul_left
    (Real.exp (parameters.sigma0 + parameters.gamma))
  rw [← tsum_mul_left]
  apply leftSummable.tsum_le_tsum (fun shift => ?_) rightSummable
  rw [← boundaryCoefficientPhaseCost_productMoment parameters moment coefficient shift]
  exact mul_le_mul_of_nonneg_left
    (boundaryScalarMultiplicationKernel_entryNorm_le
      parameters dimension coefficient moments shift)
    (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
      (pow_nonneg (annularFrequency_pos shift).le moment))

end Grad.BoundaryKernelAction
