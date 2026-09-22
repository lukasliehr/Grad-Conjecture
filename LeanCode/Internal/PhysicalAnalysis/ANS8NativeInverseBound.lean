import ANS7ExactAngularInverse

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped BigOperators Interval ContDiff Topology
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

/-- Uniform also in the integer shift; no width, cell or derivative loss. -/
def angularInverseConstant (grade : ℕ) : ℝ :=
  (2 * Real.pi * orthogonalGradeConstant grade) * (1 + orthogonalGradeConstant grade)

theorem angularInverseConstant_nonnegative (grade : ℕ) : 0 ≤ angularInverseConstant grade := by
  unfold angularInverseConstant orthogonalGradeConstant
  positivity

private theorem subtract_bound {E : Type*} [NormedAddCommGroup E]
    (first second : E) (C : ℝ) (bound : ‖second‖ ≤ C * ‖first‖) :
    ‖first - second‖ ≤ (1 + C) * ‖first‖ := by
  have triangle := norm_sub_le first second
  nlinarith

theorem shiftInverse_row_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (cell shift : ℤ) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (shiftInverseJet shift field)‖ ≤
      angularInverseConstant grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have removed : ‖apRowLinear (grade := grade) L sigma gamma ell cell
      (excludedAngularJet {-shift} field)‖ ≤
      (1 + orthogonalGradeConstant grade) * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
    rw [excluded_single_eq, map_sub]
    exact subtract_bound _ _ _
      (apAngular_row_bound (grade := grade) L sigma gamma ell cell (-shift) field)
  have kernel := apKernel_row_bound (grade := grade) L sigma gamma ell cell (shiftPrimitiveKernel shift)
    (shiftPrimitiveKernel_smooth shift) (2 * Real.pi) (by positivity)
    (shiftPrimitiveKernel_bound shift) (excludedAngularJet {-shift} field)
  change ‖apRowLinear (grade := grade) L sigma gamma ell cell (kernelRotationJet
    (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift) (excludedAngularJet {-shift} field))‖ ≤ _
  exact kernel.trans ((mul_le_mul_of_nonneg_left removed (by unfold orthogonalGradeConstant; positivity)).trans_eq
    (by unfold angularInverseConstant; ring))

theorem shiftInverse_preserves_zero_derivatives {dimension order : ℕ} (shift : ℤ)
    (field : ClosedJet dimension)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (shiftInverseJet shift field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 :=
  kernelRotationJet_preserves_zero_derivatives (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)
    (excludedAngularJet {-shift} field) (excludedAngularJet_preserves_zero_derivatives {-shift} field zeroJets) word

end Grad.ActualAngularInverse
