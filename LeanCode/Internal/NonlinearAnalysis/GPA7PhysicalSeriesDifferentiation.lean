import GPA5ForceAngularCells
import GPA6SigmaAngularCells

noncomputable section
open scoped BigOperators ContDiff
namespace Grad.ActualPhysicalAngular
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra

/-- The derivative of the entire actual axial series is obtained from a summable
cellwise bound. No infinite sum is differentiated from only a global bound. -/
theorem physicalAxialSeries_hasDerivAt
    (cells : ℤ → ℝ × ℝ → ComplexEuclidean 1) (smooth : ∀ cell, ContDiff ℝ ∞ (cells cell))
    (radius : ℝ) (physical : ℝ → ℝ → ℂ)
    (series : ∀ axialAngle angle, HasSum (fun cell => fourierPhase cell axialAngle *
      scalarCellValue (cells cell) radius angle) (physical axialAngle angle))
    (budget : ℤ → ℝ) (summable : Summable budget)
    (bound : ∀ cell angle, ‖scalarCellAngular (cells cell) radius angle‖ ≤ budget cell)
    (axialAngle angle : ℝ) :
    HasDerivAt (physical axialAngle)
      (∑' cell, fourierPhase cell axialAngle * scalarCellAngular (cells cell) radius angle) angle := by
  have derivative := hasDerivAt_tsum summable
    (fun cell time => (scalarCellAngular_hasDerivAt (cells cell) (smooth cell) radius time).const_mul
      (fourierPhase cell axialAngle))
    (fun cell time => by
      rw [norm_mul, fourierPhase_norm, one_mul]
      exact bound cell time)
    (series axialAngle 0).summable angle
  have equality : (fun time => ∑' cell, fourierPhase cell axialAngle * scalarCellValue (cells cell) radius time) =
      physical axialAngle := funext (fun time => (series axialAngle time).tsum_eq)
  rw [equality] at derivative
  exact derivative

theorem physicalAxialDerivative_coefficient
    (cells : ℤ → ℝ × ℝ → ComplexEuclidean 1) (smooth : ∀ cell, ContDiff ℝ ∞ (cells cell))
    (radius : ℝ) (physical : ℝ → ℝ → ℂ)
    (series : ∀ axialAngle angle, HasSum (fun cell => fourierPhase cell axialAngle *
      scalarCellValue (cells cell) radius angle) (physical axialAngle angle))
    (budget : ℤ → ℝ) (summable : Summable budget)
    (bound : ∀ cell angle, ‖scalarCellAngular (cells cell) radius angle‖ ≤ budget cell)
    (angle : ℝ) (cell : ℤ) :
    angularCoefficient (fun axialAngle => deriv (physical axialAngle) angle) cell =
      scalarCellAngular (cells cell) radius angle := by
  have angularNorms : Summable (fun source => ‖scalarCellAngular (cells source) radius angle‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun source => bound source angle) summable
  apply angularCoefficient_of_axialSeries _ angularNorms _
  intro axialAngle
  rw [(physicalAxialSeries_hasDerivAt cells smooth radius physical series budget summable bound axialAngle angle).deriv]
  exact (Summable.of_norm (by
    simpa only [norm_smul, fourierPhase_norm, one_mul] using angularNorms)).hasSum

theorem physicalClassicalAngular_correspondence
    (cells : ℤ → ℝ × ℝ → ComplexEuclidean 1) (smooth : ∀ cell, ContDiff ℝ ∞ (cells cell))
    (periodic : ∀ cell, Function.Periodic (cells cell) (0, 2 * Real.pi))
    (radius : ℝ) (physical : ℝ → ℝ → ℂ)
    (series : ∀ axialAngle angle, HasSum (fun cell => fourierPhase cell axialAngle *
      scalarCellValue (cells cell) radius angle) (physical axialAngle angle))
    (valueNorms : ∀ angle, Summable (fun cell => ‖scalarCellValue (cells cell) radius angle‖))
    (budget : ℤ → ℝ) (summable : Summable budget)
    (bound : ∀ cell angle, ‖scalarCellAngular (cells cell) radius angle‖ ≤ budget cell) :
    (∀ axialAngle, Differentiable ℝ (physical axialAngle)) ∧
    ∀ mode : ℤ × ℤ,
      angularCoefficient (fun angle => angularCoefficient (fun axialAngle => deriv (physical axialAngle) angle) mode.2) mode.1 =
        (Complex.I * (mode.1 : ℂ)) *
          angularCoefficient (fun angle => angularCoefficient (fun axialAngle => physical axialAngle angle) mode.2) mode.1 := by
  refine ⟨fun axialAngle angle =>
    (physicalAxialSeries_hasDerivAt cells smooth radius physical series budget summable bound axialAngle angle).differentiableAt, ?_⟩
  intro mode
  have actual (angle : ℝ) :
      angularCoefficient (fun axialAngle => physical axialAngle angle) mode.2 =
        scalarCellValue (cells mode.2) radius angle :=
    angularCoefficient_of_axialSeries _ (valueNorms angle) _
      (fun axialAngle => series axialAngle angle) mode.2
  simp_rw [physicalAxialDerivative_coefficient cells smooth radius physical series budget summable bound, actual]
  exact scalarCellAngular_fourier (cells mode.2) (smooth mode.2) (periodic mode.2) radius mode.1

end Grad.ActualPhysicalAngular
