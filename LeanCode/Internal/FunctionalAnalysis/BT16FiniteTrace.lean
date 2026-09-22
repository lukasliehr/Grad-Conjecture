import BT15IntegratedBessel

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

theorem angularCoefficient_zero {dimension : ℕ} (mode : ℤ) :
    angularCoefficient (fun _ : ℝ => (0 : ComplexEuclidean dimension)) mode = 0 := by
  rw [angularCoefficient_integral]
  simp only [smul_zero, intervalIntegral.integral_zero]

theorem finite_trace_energy_bound {dimension : ℕ} (cell : ℤ) (grade : ℕ) (gradePositive : 1 ≤ grade)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (vanishes : ∀ angle : ℝ, field (1 / 4, angle) = 0) (modes : Finset ℤ) :
    (∑ mode ∈ modes, boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
      ‖angularCoefficient (fun angle => field (0, angle)) mode‖ ^ 2) ≤
      (∑ mode ∈ modes, boundaryFrequency (mode, cell) ^ (2 * grade) * angularCoefficientEnergy field mode) +
      ∑ mode ∈ modes, boundaryFrequency (mode, cell) ^ (2 * (grade - 1)) * angularCoefficientEnergy (radialField field) mode := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro mode _
  apply half_weight_energy_bound
    (fun time => angularCoefficient (fun angle => field (time, angle)) mode)
    (fun time => angularCoefficient (fun angle => radialField field (time, angle)) mode)
    (boundaryFrequency (mode, cell)) (boundaryFrequency_pos _) grade gradePositive
    (angularCoefficient_smooth field smooth mode).continuous
    (angularCoefficient_smooth (radialField field) (radialField_smooth field smooth) mode).continuous
  · intro time _
    exact angularCoefficient_hasDerivAt field smooth mode time
  · rw [show (fun angle => field (1 / 4, angle)) = fun _ => 0 from funext vanishes]
    exact angularCoefficient_zero mode

def frequencyGradeConstant (grade : ℕ) : ℝ := (2 : ℝ) ^ grade * (2 * Real.pi)⁻¹

theorem frequencyGradeConstant_nonnegative (grade : ℕ) : 0 ≤ frequencyGradeConstant grade := by
  unfold frequencyGradeConstant
  positivity

theorem finite_trace_collar_bound {dimension : ℕ} (cell : ℤ) (grade : ℕ) (gradePositive : 1 ≤ grade)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (0, 2 * Real.pi))
    (vanishes : ∀ angle : ℝ, field (1 / 4, angle) = 0) (modes : Finset ℤ) :
    (∑ mode ∈ modes, boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
      ‖angularCoefficient (fun angle => field (0, angle)) mode‖ ^ 2) ≤
      frequencyGradeConstant grade *
        (cellFrequency cell ^ (2 * grade) * collarIntegral (fun point => ‖field point‖ ^ 2) +
          collarIntegral (fun point => ‖angularJet grade field point‖ ^ 2)) +
      frequencyGradeConstant (grade - 1) *
        (cellFrequency cell ^ (2 * (grade - 1)) * collarIntegral (fun point => ‖radialField field point‖ ^ 2) +
          collarIntegral (fun point => ‖angularJet (grade - 1) (radialField field) point‖ ^ 2)) := by
  apply (finite_trace_energy_bound cell grade gradePositive field smooth vanishes modes).trans
  exact add_le_add (finite_frequency_energy_bound cell grade field smooth periodic modes)
    (finite_frequency_energy_bound cell (grade - 1) (radialField field) (radialField_smooth field smooth)
      (radialField_periodic field periodic) modes)

end Grad.BoundaryTrace
