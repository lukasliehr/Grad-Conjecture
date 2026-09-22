import AJH1PolynomialKernelAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.BoundaryLift

variable {source target : ℕ} (parameters : PhaseParameters) (power : ℕ) (shift : ℤ × ℤ)

private theorem matrixShiftEntry_bound (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) (mode : ℤ × ℤ) :
    ‖(polynomialWeightRatio power shift mode : ℂ) • mapping‖ ≤ annularFrequency shift.1 shift.2 ^ power * ‖mapping‖ := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg (polynomialWeightRatio_nonnegative power shift mode)]
  exact mul_le_mul_of_nonneg_right (polynomialWeightRatio_bound power shift mode) (norm_nonneg _)

def polynomialMatrixShiftValue (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :
    CellL2 source →L[ℂ] CellL2 target :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (fun mode => (polynomialWeightRatio power shift mode : ℂ) • mapping)
    (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (norm_nonneg mapping))
    (matrixShiftEntry_bound power shift mapping)

def polynomialMatrixShiftLinear : (ComplexEuclidean source →L[ℂ] ComplexEuclidean target) →ₗ[ℂ]
    (CellL2 source →L[ℂ] CellL2 target) where
  toFun := polynomialMatrixShiftValue parameters power shift
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro field
    apply lp.ext
    funext mode
    change (polynomialWeightRatio power shift mode : ℂ) •
      (first (field (twoFrequencyTranslation shift mode)) + second (field (twoFrequencyTranslation shift mode))) = _
    exact smul_add _ _ _
  map_smul' scalar mapping := by
    apply ContinuousLinearMap.ext
    intro field
    apply lp.ext
    funext mode
    change (polynomialWeightRatio power shift mode : ℂ) •
      (scalar • mapping (field (twoFrequencyTranslation shift mode))) =
      scalar • ((polynomialWeightRatio power shift mode : ℂ) • mapping (field (twoFrequencyTranslation shift mode)))
    exact smul_comm _ _ _

theorem polynomialMatrixShiftLinear_bound (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :
    ‖polynomialMatrixShiftLinear parameters power shift mapping‖ ≤ annularFrequency shift.1 shift.2 ^ power * ‖mapping‖ :=
  coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift)
    (fun mode => (polynomialWeightRatio power shift mode : ℂ) • mapping)
    (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (norm_nonneg mapping))
    (matrixShiftEntry_bound power shift mapping)

/-- A fixed Fourier shift is bounded linear in its actual matrix coefficient.
This supplies genuine radial derivatives of primitive coefficient actions. -/
def polynomialMatrixShift : (ComplexEuclidean source →L[ℂ] ComplexEuclidean target) →L[ℂ]
    (CellL2 source →L[ℂ] CellL2 target) :=
  (polynomialMatrixShiftLinear parameters power shift).mkContinuous (annularFrequency shift.1 shift.2 ^ power)
    (polynomialMatrixShiftLinear_bound parameters power shift)

theorem polynomialMatrixShift_bound (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target) :
    ‖polynomialMatrixShift parameters power shift mapping‖ ≤ annularFrequency shift.1 shift.2 ^ power * ‖mapping‖ :=
  polynomialMatrixShiftLinear_bound parameters power shift mapping

theorem polynomialMatrixShift_apply (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target)
    (field : CellL2 source) (mode : ℤ × ℤ) :
    polynomialMatrixShift parameters power shift mapping field mode =
      (polynomialWeightRatio power shift mode : ℂ) • mapping (field (twoFrequencyTranslation shift mode)) := rfl

/-- The matrix-shift calculus is literally the original row/matrix action,
even when the kernel bookkeeping phase depends on the physical radius. -/
theorem polynomialShiftAction_constantEntry (kernelParameters : PhaseParameters)
    (kernel : FullTwoFrequencyKernel kernelParameters source target)
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target)
    (same : ∀ input, kernel.entry shift input = mapping) :
    polynomialShiftAction kernelParameters power kernel shift = polynomialMatrixShift parameters power shift mapping := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  change (polynomialWeightRatio power shift mode : ℂ) •
    kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode)) = _
  rw [same]
  rfl

end Grad.AnnularRadialSmoothness
