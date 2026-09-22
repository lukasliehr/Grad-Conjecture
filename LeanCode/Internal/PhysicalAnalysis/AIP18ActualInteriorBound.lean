import AIP17ActualSpectralEquation

noncomputable section

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization Grad.CircularHighRegularity Grad.InteriorFourier

def interiorFourierConstant : ℝ := sameGradeConstant 0 *
  (4 * cutoffLaplacianSourceConstant + 2 * cutoffLaplacianStateConstant)

theorem interiorFourierConstant_nonnegative : 0 ≤ interiorFourierConstant :=
  mul_nonneg (sameGradeConstant_nonnegative 0)
    (add_nonneg (mul_nonneg (by norm_num) cutoffLaplacianSourceConstant_nonnegative)
      (mul_nonneg (by norm_num) cutoffLaplacianStateConstant_nonnegative))

theorem localizedDiskField_bound (parameter : ℝ) (source : highDiskL2) :
    ‖localizedDiskField parameter source‖ ≤ 2 * cutoffLaplacianSourceConstant * ‖source‖ := by
  have bulk := (highBulk_norm_le (highRobinWeakInverse parameter source)).trans (weakSolution_bound parameter source)
  have multiplication := (diskScalar interiorCutoff.toFun interiorCutoff.smooth).le_opNorm
    (highDiskBulk (highRobinWeakInverse parameter source))
  exact multiplication.trans ((mul_le_mul_of_nonneg_left bulk cutoffLaplacianSourceConstant_nonnegative).trans_eq (by ring))

theorem localizedDiskField_RHS_bound (parameter : ℝ) (source : highDiskL2) :
    ‖localizedDiskRHS parameter source‖ + ‖localizedDiskField parameter source‖ ≤
      (4 * cutoffLaplacianSourceConstant + 2 * cutoffLaplacianStateConstant) * (1 + parameter ^ 2) * ‖source‖ := by
  have laplacian := localizedDiskLaplacian_bound (highRobinWeakInverse parameter source).val
    (weakLaplacianValue parameter source)
  have sourceBound := mul_le_mul_of_nonneg_left (actualWeakLaplacian_bound parameter source)
    cutoffLaplacianSourceConstant_nonnegative
  have stateBound := mul_le_mul_of_nonneg_left (weakSolution_bound parameter source)
    cutoffLaplacianStateConstant_nonnegative
  change cutoffLaplacianStateConstant * ‖(highRobinWeakInverse parameter source).val‖ ≤
    cutoffLaplacianStateConstant * (2 * ‖source‖) at stateBound
  have bulkBound := localizedDiskField_bound parameter source
  change ‖localizedDiskRHS parameter source‖ ≤ _ at laplacian
  nlinarith [mul_nonneg cutoffLaplacianSourceConstant_nonnegative (norm_nonneg source),
    mul_nonneg cutoffLaplacianSourceConstant_nonnegative (mul_nonneg (sq_nonneg parameter) (norm_nonneg source)),
    mul_nonneg cutoffLaplacianStateConstant_nonnegative (mul_nonneg (sq_nonneg parameter) (norm_nonneg source))]

/-- Uniform-in-k polynomial estimate for the constructed two-derivative
Fourier representative of the actual localized weak Robin inverse. -/
theorem actualInteriorFourier_consumer (parameters : PhaseParameters) (parameter : ℝ) (source : highDiskL2) :
    ∃ higher : JGrade (ComplexEuclidean 1) 2,
      inclusion 2 0 (by omega) higher = diskFourier parameters (localizedDiskField parameter source) ∧
      ‖higher‖ ≤ interiorFourierConstant * (1 + parameter ^ 2) * ‖source‖ := by
  obtain ⟨higher, sameField, bound⟩ := actualInteriorFourier_H2 parameters parameter source
  refine ⟨higher, sameField, bound.trans ?_⟩
  calc
    _ ≤ sameGradeConstant 0 * (‖localizedDiskRHS parameter source‖ + ‖localizedDiskField parameter source‖) :=
      (add_le_add (diskFourier_bound parameters _) (diskFourier_bound parameters _)).trans_eq (mul_add _ _ _).symm
    _ ≤ sameGradeConstant 0 *
        ((4 * cutoffLaplacianSourceConstant + 2 * cutoffLaplacianStateConstant) * (1 + parameter ^ 2) * ‖source‖) :=
      mul_le_mul_of_nonneg_left (localizedDiskField_RHS_bound parameter source) (sameGradeConstant_nonnegative 0)
    _ = _ := by unfold interiorFourierConstant; ring

end Grad.InteriorPeriodization
