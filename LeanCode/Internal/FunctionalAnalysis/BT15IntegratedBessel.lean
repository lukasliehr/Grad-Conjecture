import BT14FrequencyEnergy

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

def angularCoefficientEnergy {dimension : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension) (mode : ℤ) : ℝ :=
  ∫ time in (0 : ℝ)..(1 / 4 : ℝ), ‖angularCoefficient (fun angle => field (time, angle)) mode‖ ^ 2

theorem angularCoefficientEnergy_nonnegative {dimension : ℕ}
    (field : ℝ × ℝ → ComplexEuclidean dimension) (mode : ℤ) : 0 ≤ angularCoefficientEnergy field mode := by
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)

theorem integrated_angular_bessel {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) * angularCoefficientEnergy field mode) ≤
      (2 * Real.pi)⁻¹ * collarIntegral (fun point => ‖angularJet order field point‖ ^ 2) := by
  have coefficientContinuous (mode : ℤ) : Continuous (fun time =>
      |(mode : ℝ)| ^ (2 * order) * ‖angularCoefficient (fun angle => field (time, angle)) mode‖ ^ 2) :=
    continuous_const.mul ((angularCoefficient_smooth field smooth mode).continuous.norm.pow 2)
  have jetContinuous : Continuous (fun point => ‖angularJet order field point‖ ^ 2) :=
    (angularJet_smooth order field smooth).continuous.norm.pow 2
  have angularIntegralContinuous : Continuous (fun time =>
      ∫ angle in -Real.pi..Real.pi, ‖angularJet order field (time, angle)‖ ^ 2) :=
    timeIntegral_continuous (fun point => ‖angularJet order field (point.2, point.1)‖ ^ 2)
      (jetContinuous.comp continuous_swap) (-Real.pi) Real.pi (neg_lt_self Real.pi_pos).le
  have comparison := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun time => ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) *
      ‖angularCoefficient (fun angle => field (time, angle)) mode‖ ^ 2)
    (g := fun time => (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi,
      ‖angularJet order field (time, angle)‖ ^ 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    ((continuous_finsetSum modes (fun mode _ => coefficientContinuous mode)).intervalIntegrable _ _)
    ((continuous_const.mul angularIntegralContinuous).intervalIntegrable _ _)
    (fun time _ => angularJet_bessel_finite order field smooth periodic time modes)
  rw [intervalIntegral.integral_finsetSum (fun mode _ => (coefficientContinuous mode).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, collarIntegral_swap _ jetContinuous] at comparison
  simpa only [intervalIntegral.integral_const_mul, angularCoefficientEnergy] using comparison

theorem integrated_angular_bessel_zero {dimension : ℕ}
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (modes : Finset ℤ) :
    (∑ mode ∈ modes, angularCoefficientEnergy field mode) ≤
      (2 * Real.pi)⁻¹ * collarIntegral (fun point => ‖field point‖ ^ 2) := by
  simpa only [Nat.mul_zero, pow_zero, one_mul, angularJet_zero] using
    integrated_angular_bessel 0 field smooth periodic modes

theorem finite_frequency_energy_bound {dimension : ℕ} (cell : ℤ) (grade : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (modes : Finset ℤ) :
    (∑ mode ∈ modes, boundaryFrequency (mode, cell) ^ (2 * grade) * angularCoefficientEnergy field mode) ≤
      ((2 : ℝ) ^ grade * (2 * Real.pi)⁻¹) *
        (cellFrequency cell ^ (2 * grade) * collarIntegral (fun point => ‖field point‖ ^ 2) +
          collarIntegral (fun point => ‖angularJet grade field point‖ ^ 2)) := by
  have frequencyComparison : (∑ mode ∈ modes,
      boundaryFrequency (mode, cell) ^ (2 * grade) * angularCoefficientEnergy field mode) ≤
      (2 : ℝ) ^ grade * (cellFrequency cell ^ (2 * grade) * (∑ mode ∈ modes, angularCoefficientEnergy field mode) +
        ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * grade) * angularCoefficientEnergy field mode) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro mode _
    simpa only [mul_add, add_mul, mul_assoc] using mul_le_mul_of_nonneg_right
      (boundaryFrequency_even_bound (mode, cell) grade) (angularCoefficientEnergy_nonnegative field mode)
  have zeroBound := integrated_angular_bessel_zero field smooth periodic modes
  have topBound := integrated_angular_bessel grade field smooth periodic modes
  apply frequencyComparison.trans
  calc
    _ ≤ (2 : ℝ) ^ grade *
        (cellFrequency cell ^ (2 * grade) * ((2 * Real.pi)⁻¹ * collarIntegral (fun point => ‖field point‖ ^ 2)) +
          (2 * Real.pi)⁻¹ * collarIntegral (fun point => ‖angularJet grade field point‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left zeroBound (pow_nonneg (cellFrequency_pos cell).le _)) topBound) (by positivity)
    _ = _ := by ring

end Grad.BoundaryTrace
