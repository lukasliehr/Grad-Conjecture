import AXF18RadialSupport

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.QuotientProjection Grad.NonlinearQuotientBounds
open Grad.Constraints.Gauges
open Grad.NonlinearProduct

variable {parameters : PhaseParameters}

def cartesianSpinFirst : SmoothQuotient parameters →ₗ[ℂ] ACore parameters 1 :=
  (1 / 2 : ℂ) •
    ((LinearMap.proj (0 : Fin 4) : SmoothQuotient parameters →ₗ[ℂ] ACore parameters 1) + LinearMap.proj 1)

def cartesianSpinSecond : SmoothQuotient parameters →ₗ[ℂ] ACore parameters 1 :=
  (-Complex.I / 2) •
    ((LinearMap.proj (0 : Fin 4) : SmoothQuotient parameters →ₗ[ℂ] ACore parameters 1) - LinearMap.proj 1)

theorem cartesianSpin_reconstruct_zero (source : SmoothQuotient parameters) :
    cartesianSpinFirst source + Complex.I • cartesianSpinSecond source = source 0 := by
  change (1 / 2 : ℂ) • (source 0 + source 1) +
    Complex.I • ((-Complex.I / 2) • (source 0 - source 1)) = source 0
  rw [smul_smul]
  have factor : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    calc _ = -(Complex.I * Complex.I) / 2 := by ring
         _ = (1 / 2 : ℂ) := by rw [Complex.I_mul_I]; norm_num
  rw [factor]
  module

theorem cartesianSpin_reconstruct_one (source : SmoothQuotient parameters) :
    cartesianSpinFirst source - Complex.I • cartesianSpinSecond source = source 1 := by
  change (1 / 2 : ℂ) • (source 0 + source 1) -
    Complex.I • ((-Complex.I / 2) • (source 0 - source 1)) = source 1
  rw [smul_smul]
  have factor : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    calc _ = -(Complex.I * Complex.I) / 2 := by ring
         _ = (1 / 2 : ℂ) := by rw [Complex.I_mul_I]; norm_num
  rw [factor]
  module

/-- Exact BS3 vector weight in the two original scalar-component grades.
The A^q(C^2) tuple isometry remains a separate correspondence step. -/
theorem originalSpin_cartesian_components_norm (parameters : PhaseParameters)
    (grade : ℕ) (source : SmoothQuotient parameters) :
    quotientNorm parameters grade source ^ 2 =
      2 * (originalGradeNorm grade (cartesianSpinFirst source) ^ 2 +
        originalGradeNorm grade (cartesianSpinSecond source) ^ 2) +
          originalGradeNorm grade (source 2) ^ 2 + originalGradeNorm grade (source 3) ^ 2 := by
  let first : GradeCore parameters 1 grade := GradeCore.ofCoreLinear (cartesianSpinFirst source)
  let second : GradeCore parameters 1 grade := GradeCore.ofCoreLinear (cartesianSpinSecond source)
  have parallelogram := parallelogram_law_with_norm ℂ first (Complex.I • second)
  simp only [norm_smul, Complex.norm_I, one_mul] at parallelogram
  change originalGradeNorm grade (cartesianSpinFirst source + Complex.I • cartesianSpinSecond source) ^ 2 +
    originalGradeNorm grade (cartesianSpinFirst source - Complex.I • cartesianSpinSecond source) ^ 2 =
      2 * (originalGradeNorm grade (cartesianSpinFirst source) ^ 2 +
        originalGradeNorm grade (cartesianSpinSecond source) ^ 2) at parallelogram
  rw [cartesianSpin_reconstruct_zero, cartesianSpin_reconstruct_one] at parallelogram
  rw [quotientNorm_sq, Fin.sum_univ_four]
  nlinarith

end Grad.FlatSourceProjection
