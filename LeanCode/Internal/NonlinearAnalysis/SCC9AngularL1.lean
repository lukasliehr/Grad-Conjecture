import BT11AngularJets
import FT3Reconstruction

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.FourierGrade
open Grad.DiskExtension.Operator

def angularL1Constant : ℝ := Real.sqrt (2 * ∑' mode, integerSquareDecay mode)

theorem angularL1Constant_nonnegative : 0 ≤ angularL1Constant := Real.sqrt_nonneg _

theorem angular_finite_cauchy (modes : Finset ℤ) (value : ℤ → ℝ) :
    (∑ mode ∈ modes, value mode) ^ 2 ≤
      (∑' mode, integerSquareDecay mode) *
        ∑ mode ∈ modes, (1 + (mode : ℝ) ^ 2) * value mode ^ 2 := by
  have cauchy := weighted_cauchy_finset modes integerSquareDecay
    (fun mode => (1 + (mode : ℝ) ^ 2) * value mode)
    (fun mode _ => integerSquareDecay_nonneg mode)
  have first (mode : ℤ) : integerSquareDecay mode *
      ((1 + (mode : ℝ) ^ 2) * value mode) = value mode := by
    unfold integerSquareDecay
    field_simp
  have second (mode : ℤ) : integerSquareDecay mode *
      ((1 + (mode : ℝ) ^ 2) * value mode) ^ 2 =
      (1 + (mode : ℝ) ^ 2) * value mode ^ 2 := by
    unfold integerSquareDecay
    field_simp
  simp_rw [first, second] at cauchy
  exact cauchy.trans (mul_le_mul_of_nonneg_right
    (integerSquareDecay_summable.sum_le_tsum modes (fun mode _ => integerSquareDecay_nonneg mode))
    (Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))))

theorem angular_scaled_bessel_sup {dimension : ℕ}
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field)
    (scale bound : ℝ) (scaleNonnegative : 0 ≤ scale)
    (pointBound : ∀ angle ∈ Icc (-Real.pi) Real.pi, scale * ‖field angle‖ ≤ bound)
    (modes : Finset ℤ) :
    ∑ mode ∈ modes, (scale * ‖angularCoefficient field mode‖) ^ 2 ≤ bound ^ 2 := by
  have bessel := mul_le_mul_of_nonneg_left (angular_bessel_finite field continuousField modes)
    (sq_nonneg scale)
  have integrable : IntervalIntegrable (fun angle => scale ^ 2 * ‖field angle‖ ^ 2)
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul (continuousField.norm.pow 2)).intervalIntegrable _ _
  have integralBound := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun angle => scale ^ 2 * ‖field angle‖ ^ 2) (g := fun _ => bound ^ 2)
    (neg_lt_self Real.pi_pos).le integrable (intervalIntegrable_const)
    (fun angle inside => by
      simpa only [mul_pow] using pow_le_pow_left₀
        (mul_nonneg scaleNonnegative (norm_nonneg _)) (pointBound angle inside) 2)
  have averaged := mul_le_mul_of_nonneg_left integralBound
    (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  rw [intervalIntegral.integral_const, smul_eq_mul] at averaged
  have period : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have cancellation : (2 * Real.pi)⁻¹ * ((Real.pi - -Real.pi) * bound ^ 2) = bound ^ 2 := by
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, ← mul_assoc,
      inv_mul_cancel₀ period.ne', one_mul]
  rw [cancellation, intervalIntegral.integral_const_mul] at averaged
  calc
    _ = scale ^ 2 * ∑ mode ∈ modes, ‖angularCoefficient field mode‖ ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ _ := bessel
    _ ≤ bound ^ 2 := by simpa only [mul_left_comm] using averaged

/-- One angular derivative suffices for absolute Fourier summability.
The supplied pointwise scale stays inside both energy estimates. -/
theorem angular_l1_finite {dimension : ℕ}
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi))
    (jetOrder : ℕ)
    (radius scale bound : ℝ) (scaleNonnegative : 0 ≤ scale) (boundNonnegative : 0 ≤ bound)
    (pointBound : ∀ order : Fin 2, ∀ angle ∈ Icc (-Real.pi) Real.pi,
      scale * ‖angularJet (jetOrder + order.val) field (radius, angle)‖ ≤ bound)
    (modes : Finset ℤ) :
    ∑ mode ∈ modes, scale *
      ‖angularCoefficient (fun angle => angularJet jetOrder field (radius, angle)) mode‖ ≤
      angularL1Constant * bound := by
  let value := fun mode => scale *
    ‖angularCoefficient (fun angle => angularJet jetOrder field (radius, angle)) mode‖
  have low := angular_scaled_bessel_sup (fun angle => angularJet jetOrder field (radius, angle))
    ((angularJet_smooth jetOrder field smooth).continuous.comp (continuous_const.prodMk continuous_id))
    scale bound scaleNonnegative (pointBound 0) modes
  have high := angular_scaled_bessel_sup (fun angle => angularJet (jetOrder + 1) field (radius, angle))
    ((angularJet_smooth (jetOrder + 1) field smooth).continuous.comp (continuous_const.prodMk continuous_id))
    scale bound scaleNonnegative (pointBound 1) modes
  have normIdentity (mode : ℤ) :
      ‖angularCoefficient (fun angle => angularJet (jetOrder + 1) field (radius, angle)) mode‖ =
        |(mode : ℝ)| *
          ‖angularCoefficient (fun angle => angularJet jetOrder field (radius, angle)) mode‖ :=
    angularCoefficient_derivative_norm _ _
      ((angularJet_smooth jetOrder field smooth).continuous.comp (continuous_const.prodMk continuous_id))
      ((angularJet_smooth (jetOrder + 1) field smooth).continuous.comp (continuous_const.prodMk continuous_id))
      (angularJet_hasDerivAt jetOrder field smooth radius)
      (angularJet_endpoint jetOrder field periodic radius) mode
  have energy : (∑ mode ∈ modes, (1 + (mode : ℝ) ^ 2) * value mode ^ 2) ≤ 2 * bound ^ 2 := by
    calc
      _ = (∑ mode ∈ modes, value mode ^ 2) +
          ∑ mode ∈ modes, (scale *
            ‖angularCoefficient (fun angle => angularJet (jetOrder + 1) field (radius, angle)) mode‖) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro mode _
        rw [normIdentity]
        dsimp [value]
        nlinarith [sq_abs (mode : ℝ)]
      _ ≤ _ := by dsimp [value]; linarith
  have squared := (angular_finite_cauchy modes value).trans
    (mul_le_mul_of_nonneg_left energy (tsum_nonneg integerSquareDecay_nonneg))
  have constantSquare : angularL1Constant ^ 2 = 2 * ∑' mode, integerSquareDecay mode := by
    exact Real.sq_sqrt (mul_nonneg (by norm_num) (tsum_nonneg integerSquareDecay_nonneg))
  have positiveRhs := mul_nonneg angularL1Constant_nonnegative boundNonnegative
  change (∑ mode ∈ modes, value mode) ≤ _
  nlinarith [sq_nonneg ((∑ mode ∈ modes, value mode) - angularL1Constant * bound)]

end Grad.SourceCollarCoefficients
