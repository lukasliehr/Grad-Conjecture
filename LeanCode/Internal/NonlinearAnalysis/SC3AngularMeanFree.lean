import SC2PhysicalCofactor

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped Interval

namespace Grad.SourceCollar

/-- Normalized angular average on one physical polar circle. -/
def sourceAngularAverage (field : ℝ → ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi, field angle

/-- The literal `P = I - Π₀` used in BS30. -/
def sourceAngularMeanFree (field : ℝ → ℂ) : ℝ → ℂ :=
  fun angle => field angle - sourceAngularAverage field

theorem sourceAngularMeanFree_intervalIntegrable {field : ℝ → ℂ}
    (integrable : IntervalIntegrable field volume 0 (2 * Real.pi)) :
    IntervalIntegrable (sourceAngularMeanFree field) volume 0 (2 * Real.pi) :=
  integrable.sub intervalIntegrable_const

/-- `P` has zero angular mean. -/
theorem sourceAngularAverage_meanFree {field : ℝ → ℂ}
    (integrable : IntervalIntegrable field volume 0 (2 * Real.pi)) :
    sourceAngularAverage (sourceAngularMeanFree field) = 0 := by
  unfold sourceAngularAverage sourceAngularMeanFree
  rw [intervalIntegral.integral_sub integrable intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_sub, smul_smul]
  rw [inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  change sourceAngularAverage field - sourceAngularAverage field = 0
  exact sub_self _

theorem sourceAngularMeanFree_of_mean_zero {field : ℝ → ℂ}
    (meanZero : sourceAngularAverage field = 0) :
    sourceAngularMeanFree field = field := by
  funext angle
  simp [sourceAngularMeanFree, meanZero]

theorem sourceAngularAverage_const_mul (scalar : ℂ) (field : ℝ → ℂ) :
    sourceAngularAverage (fun angle => scalar * field angle) =
      scalar * sourceAngularAverage field := by
  unfold sourceAngularAverage
  rw [intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem sourceAngularAverage_div (field : ℝ → ℂ) (scalar : ℂ) :
    sourceAngularAverage (fun angle => field angle / scalar) =
      sourceAngularAverage field / scalar := by
  simp only [div_eq_inv_mul]
  rw [sourceAngularAverage_const_mul]

/-- Adding a mean-free correction preserves a zero angular mean. -/
theorem sourceAngularAverage_add_meanFree {field correction : ℝ → ℂ}
    (fieldIntegrable : IntervalIntegrable field volume 0 (2 * Real.pi))
    (correctionIntegrable : IntervalIntegrable correction volume 0 (2 * Real.pi))
    (fieldMean : sourceAngularAverage field = 0) :
    sourceAngularAverage (fun angle => field angle + sourceAngularMeanFree correction angle) = 0 := by
  unfold sourceAngularAverage
  rw [intervalIntegral.integral_add fieldIntegrable
    (sourceAngularMeanFree_intervalIntegrable correctionIntegrable), smul_add]
  change sourceAngularAverage field + sourceAngularAverage (sourceAngularMeanFree correction) = 0
  rw [fieldMean, sourceAngularAverage_meanFree correctionIntegrable, add_zero]

end Grad.SourceCollar
