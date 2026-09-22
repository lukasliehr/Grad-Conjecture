import ANR52ActualClosedCollarConsumer

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

/-- The accepted continuous coefficient of the same actual weak inverse. -/
def actualRadialValue (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) : C(ℝ, ComplexEuclidean 1) :=
  radialSectionExtension 1 lower bounded.le
    (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val)

/-- Literal second derivative solved from AN19, on both closed endpoints. -/
theorem actualRadial_second_eq (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (high : mode ∉ lowAngularModes)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1))
        (Icc lower 1) radius =
      -(radius⁻¹ • derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius) +
      ((mode : ℝ) ^ 2 / radius ^ 2) • actualRadialValue lower positive bounded mode parameter source radius +
      (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
        actualRadialValue lower positive bounded mode parameter source radius - diskCoreRadialCurve mode core radius := by
  have equation := weakInverse_literal_radialEquation lower positive bounded parameter source mode high core same radius inside
  change -derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1))
      (Icc lower 1) radius -
      radius⁻¹ • derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius +
      ((mode : ℝ) ^ 2 / radius ^ 2) • actualRadialValue lower positive bounded mode parameter source radius +
      (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
        actualRadialValue lower positive bounded mode parameter source radius = diskCoreRadialCurve mode core radius at equation
  calc
    _ = derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1))
        (Icc lower 1) radius +
        ((-derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1))
          (Icc lower 1) radius -
          radius⁻¹ • derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius +
          ((mode : ℝ) ^ 2 / radius ^ 2) • actualRadialValue lower positive bounded mode parameter source radius +
          (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
            actualRadialValue lower positive bounded mode parameter source radius) - diskCoreRadialCurve mode core radius) := by
      rw [equation, sub_self, add_zero]
    _ = _ := by abel

private theorem norm_add_sq {E : Type*} [SeminormedAddCommGroup E] (first second : E) :
    ‖first + second‖ ^ 2 ≤ 2 * (‖first‖ ^ 2 + ‖second‖ ^ 2) := by
  have bound := norm_add_le first second
  have nonnegative := norm_nonneg (first + second)
  nlinarith [sq_nonneg (‖first‖ - ‖second‖)]

theorem norm_four_sq {E : Type*} [SeminormedAddCommGroup E] (first second third fourth : E) :
    ‖first + second + third + fourth‖ ^ 2 ≤
      4 * (‖first‖ ^ 2 + ‖second‖ ^ 2 + ‖third‖ ^ 2 + ‖fourth‖ ^ 2) := by
  have outer := norm_add_sq (first + second) (third + fourth)
  have left := norm_add_sq first second
  have right := norm_add_sq third fourth
  rw [← add_assoc] at outer
  linarith

/-- Pointwise four-term squared estimate for the genuine second derivative.
The source is the literal original Fourier coefficient. -/
theorem actualRadial_second_pointwise (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (high : mode ∉ lowAngularModes)
    (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖derivWithin (derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1))
        (Icc lower 1) radius‖ ^ 2 ≤
      4 * (‖radius⁻¹ • derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius‖ ^ 2 +
        ‖((mode : ℝ) ^ 2 / radius ^ 2) • actualRadialValue lower positive bounded mode parameter source radius‖ ^ 2 +
        ‖(((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
          actualRadialValue lower positive bounded mode parameter source radius‖ ^ 2 + ‖diskCoreRadialCurve mode core radius‖ ^ 2) := by
  rw [actualRadial_second_eq lower positive bounded parameter source mode high core same radius inside, sub_eq_add_neg]
  simpa only [norm_neg] using norm_four_sq
    (-(radius⁻¹ • derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius))
    (((mode : ℝ) ^ 2 / radius ^ 2) • actualRadialValue lower positive bounded mode parameter source radius)
    ((((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) •
      actualRadialValue lower positive bounded mode parameter source radius) (-diskCoreRadialCurve mode core radius)

end Grad.CircularHighRegularity
