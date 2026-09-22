import GC21Boundary

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.BoundaryTrace

theorem apBoundaryFrequency_even_bound (L ell : ℝ) (mode : ℤ × ℤ) (order : ℕ) :
    apBoundaryFrequency L ell mode ^ (2 * order) ≤ (2 : ℝ) ^ order *
      (scaledCellWeight L ell mode.2 ^ (2 * order) + |(mode.1 : ℝ)| ^ (2 * order)) := by
  have identity : apBoundaryFrequency L ell mode ^ 2 =
      scaledCellWeight L ell mode.2 ^ 2 + |(mode.1 : ℝ)| ^ 2 := by
    rw [apBoundaryFrequency_sq, scaledCellWeight, Real.sq_sqrt (by positivity), sq_abs]
    ring
  rw [pow_mul, identity]
  simpa only [← pow_mul] using two_term_pow_bound
    (scaledCellWeight L ell mode.2 ^ 2) (|(mode.1 : ℝ)| ^ 2) (sq_nonneg _) (sq_nonneg _) order

theorem apFiniteFrequencyEnergy {dimension : ℕ} (L ell : ℝ) (cell : ℤ) (grade : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi)) (modes : Finset ℤ) :
    (∑ mode ∈ modes, apBoundaryFrequency L ell (mode, cell) ^ (2 * grade) * angularCoefficientEnergy field mode) ≤
      frequencyGradeConstant grade *
        (scaledCellWeight L ell cell ^ (2 * grade) * collarIntegral (fun point => ‖field point‖ ^ 2) +
          collarIntegral (fun point => ‖angularJet grade field point‖ ^ 2)) := by
  have comparison : (∑ mode ∈ modes,
      apBoundaryFrequency L ell (mode, cell) ^ (2 * grade) * angularCoefficientEnergy field mode) ≤
      (2 : ℝ) ^ grade * (scaledCellWeight L ell cell ^ (2 * grade) *
        (∑ mode ∈ modes, angularCoefficientEnergy field mode) +
        ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * grade) * angularCoefficientEnergy field mode) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro mode _
    simpa only [mul_add, add_mul, mul_assoc] using mul_le_mul_of_nonneg_right
      (apBoundaryFrequency_even_bound L ell (mode, cell) grade) (angularCoefficientEnergy_nonnegative field mode)
  have zeroBound := integrated_angular_bessel_zero field smooth periodic modes
  have topBound := integrated_angular_bessel grade field smooth periodic modes
  apply comparison.trans
  calc
    _ ≤ (2 : ℝ) ^ grade *
        (scaledCellWeight L ell cell ^ (2 * grade) *
          ((2 * Real.pi)⁻¹ * collarIntegral (fun point => ‖field point‖ ^ 2)) +
          (2 * Real.pi)⁻¹ * collarIntegral (fun point => ‖angularJet grade field point‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left zeroBound (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)) topBound) (by positivity)
    _ = _ := by unfold frequencyGradeConstant; ring

theorem apFiniteTraceEnergy {dimension : ℕ} (L ell : ℝ) (cell : ℤ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (vanishes : ∀ angle : ℝ, field (1 / 4, angle) = 0)
    (modes : Finset ℤ) :
    (∑ mode ∈ modes, apBoundaryFrequency L ell (mode, cell) ^ (2 * grade - 1) *
      ‖angularCoefficient (fun angle => field (0, angle)) mode‖ ^ 2) ≤
      (∑ mode ∈ modes, apBoundaryFrequency L ell (mode, cell) ^ (2 * grade) * angularCoefficientEnergy field mode) +
      ∑ mode ∈ modes, apBoundaryFrequency L ell (mode, cell) ^ (2 * (grade - 1)) * angularCoefficientEnergy (radialField field) mode := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro mode _
  apply half_weight_energy_bound
    (fun time => angularCoefficient (fun angle => field (time, angle)) mode)
    (fun time => angularCoefficient (fun angle => radialField field (time, angle)) mode)
    (apBoundaryFrequency L ell (mode, cell)) (apBoundaryFrequency_pos L ell _) grade gradePositive
    (angularCoefficient_smooth field smooth mode).continuous
    (angularCoefficient_smooth (radialField field) (radialField_smooth field smooth) mode).continuous
  · intro time _
    exact angularCoefficient_hasDerivAt field smooth mode time
  · rw [show (fun angle => field (1 / 4, angle)) = fun _ => 0 from funext vanishes]
    exact angularCoefficient_zero mode

theorem apFiniteTraceCollarBound {dimension : ℕ} (L ell : ℝ) (cell : ℤ) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (periodic : Function.Periodic field (0, 2 * Real.pi))
    (vanishes : ∀ angle : ℝ, field (1 / 4, angle) = 0) (modes : Finset ℤ) :
    (∑ mode ∈ modes, apBoundaryFrequency L ell (mode, cell) ^ (2 * grade - 1) *
      ‖angularCoefficient (fun angle => field (0, angle)) mode‖ ^ 2) ≤
      frequencyGradeConstant grade *
        (scaledCellWeight L ell cell ^ (2 * grade) * collarIntegral (fun point => ‖field point‖ ^ 2) +
          collarIntegral (fun point => ‖angularJet grade field point‖ ^ 2)) +
      frequencyGradeConstant (grade - 1) *
        (scaledCellWeight L ell cell ^ (2 * (grade - 1)) * collarIntegral (fun point => ‖radialField field point‖ ^ 2) +
          collarIntegral (fun point => ‖angularJet (grade - 1) (radialField field) point‖ ^ 2)) := by
  apply (apFiniteTraceEnergy L ell cell grade gradePositive field smooth vanishes modes).trans
  exact add_le_add (apFiniteFrequencyEnergy L ell cell grade field smooth periodic modes)
    (apFiniteFrequencyEnergy L ell cell (grade - 1) (radialField field) (radialField_smooth field smooth)
      (radialField_periodic field periodic) modes)

end Grad.GaugeCoefficients.Physical.WeightedTrace
