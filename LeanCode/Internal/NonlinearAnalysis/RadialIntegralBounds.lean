import RadialIntegralFTC

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Grad.NonlinearQuotient

open Grad.MainTarget

theorem radialKernel_nonnegative {scale : ℝ} (scaleIn : scale ∈ Icc (0 : ℝ) 1) :
    0 ≤ Real.negMulLog scale := by
  have logarithm := Real.log_nonpos scaleIn.1 scaleIn.2
  dsimp [Real.negMulLog]
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr scaleIn.1) logarithm

theorem radialIntegral_norm_le
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → Target) (point : Plane) (bound : ℝ)
    (continuous : ContinuousOn (fun scale : ℝ => field (scale • point)) (Icc 0 1))
    (bounded : ∀ scale ∈ Icc (0 : ℝ) 1, ‖field (scale • point)‖ ≤ bound) :
    ‖radialIntegral field point‖ ≤ bound / 4 := by
  have integrandContinuous : ContinuousOn
      (fun scale => Real.negMulLog scale • field (scale • point)) (Icc 0 1) := by
    intro scale scaleIn
    exact Real.continuous_negMulLog.continuousAt.continuousWithinAt.smul
      (continuous scale scaleIn)
  have majorantContinuous : Continuous (fun scale => Real.negMulLog scale * bound) :=
    Real.continuous_negMulLog.mul continuous_const
  calc
    ‖radialIntegral field point‖ ≤
        ∫ scale in (0 : ℝ)..1, ‖Real.negMulLog scale • field (scale • point)‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ scale in (0 : ℝ)..1, Real.negMulLog scale * bound := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (ContinuousOn.intervalIntegrable_of_Icc zero_le_one integrandContinuous.norm)
        (majorantContinuous.intervalIntegrable 0 1)
      intro scale scaleIn
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialKernel_nonnegative scaleIn)]
      exact mul_le_mul_of_nonneg_left (bounded scale scaleIn) (radialKernel_nonnegative scaleIn)
    _ = bound / 4 := by
      rw [intervalIntegral.integral_mul_const, integral_radialKernel]
      ring

end Grad.NonlinearQuotient
