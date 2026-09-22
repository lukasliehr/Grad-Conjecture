import ARW5ActualFourierRows

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualRadialWords
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualOuterCollar Grad.CollarCartesian Grad.BoundaryLift

/-- The exact collar change of variable with its actual radial Jacobian. -/
theorem reflected_integral_le_radial (density : ℝ → ℝ)
    (continuousDensity : ContinuousOn density (Icc (1 / 2 : ℝ) 1))
    (nonnegative : ∀ radius ∈ Icc (1 / 2 : ℝ) 1, 0 ≤ density radius) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), density (1 - time)) ≤
      2 * ∫ radius in (1 / 2 : ℝ)..1, radius * density radius := by
  have substitution := intervalIntegral.integral_comp_sub_left density (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) 1
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, sub_zero] at substitution
  rw [substitution]
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) continuousDensity)
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (continuousOn_const.mul (continuousOn_id.mul continuousDensity))) (by
      intro radius inside
      change density radius ≤ 2 * (radius * density radius)
      nlinarith [mul_nonneg (by linarith [inside.1] : 0 ≤ 2 * radius - 1) (nonnegative radius inside)])
  simp only [Pi.mul_apply] at comparison
  rw [intervalIntegral.integral_const_mul] at comparison
  exact comparison

def actualRadialCountEnergy (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (radial : ℕ) : ℝ :=
  ∫ radius in (1 / 2 : ℝ)..1, radius *
    ‖iteratedDerivWithin radial (actualProfile mode parameter source) (Icc (1 / 2 : ℝ) 1) radius‖ ^ 2

theorem actualRadialCountEnergy_nonnegative (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (radial : ℕ) :
    0 ≤ actualRadialCountEnergy parameter source mode radial :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ inside => mul_nonneg (by linarith [inside.1]) (sq_nonneg _))

theorem actualWordRows_radial_integral (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (mode : ℤ) (high : mode ∉ Grad.Constraints.lowAngularModes) (order : ℕ) (word : CartesianWord order) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖actualWordRows parameter source order word mode time‖ ^ 2) ≤
      2 * (|(mode : ℝ)| ^ (2 * wordCount word 1) * actualRadialCountEnergy parameter source mode (wordCount word 0)) := by
  have continuousDensity := ((actualProfile_smooth mode high parameter source core same).continuousOn_iteratedDerivWithin
    (m := wordCount word 0) (by exact_mod_cast (le_top : (wordCount word 0 : ℕ∞) ≤ ⊤))
    (uniqueDiffOn_Icc (by norm_num : (1 / 2 : ℝ) < 1))).norm.pow 2
  have comparison := reflected_integral_le_radial _ continuousDensity (fun _ _ => sq_nonneg _)
  simp only [Pi.pow_apply] at comparison
  simp only [actualWordRows, if_pos high, wordAmplitude_norm_sq]
  rw [intervalIntegral.integral_const_mul]
  exact (mul_le_mul_of_nonneg_left comparison (pow_nonneg (abs_nonneg _) _)).trans_eq (by
    unfold actualRadialCountEnergy
    ring)

end Grad.ActualRadialWords
