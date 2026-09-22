import GC21CollarDensity
import GC21FrequencyEnergy

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.BoundaryTrace

/-- Uniform exact AP2-to-AP3 estimate before either Fourier summation or
completion. Every actual Cartesian derivative and the scaled kappa remain. -/
theorem apFiniteCellTrace {dimension : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (grade : ℕ) (gradePositive : 1 ≤ grade) (field : ClosedJet dimension) (modes : Finset ℤ) :
    (∑ mode ∈ modes, apBoundaryFrequency L ell (mode, cell) ^ (2 * grade - 1) *
      ‖fourierCoeff (fun angle : CellCircle =>
        (apWeightedJet sigma gamma ell cell field).value (boundaryDiskPoint angle)) mode‖ ^ 2) ≤
      traceCellConstant grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
  let actual := collarField (smoothClosedExtension (apWeightedJet sigma gamma ell cell field))
  have smooth : ContDiff ℝ ∞ actual := collarField_smooth (smoothClosedExtension_smooth _)
  have preliminary := apFiniteTraceCollarBound L ell cell grade gradePositive actual smooth
    (collarField_periodic _) (collarField_endpoint _) modes
  have zeroBound := apWeightedCollarIntegral (grade := grade) (order := 0) L sigma gamma ell cell field (Nat.zero_le _)
  simp only [Nat.sub_zero, norm_iteratedFDeriv_zero] at zeroBound
  have highBound := apWeightedCollarIntegral (grade := grade) (order := grade) L sigma gamma ell cell field le_rfl
  simp only [Nat.sub_self, Nat.mul_zero, pow_zero, one_mul] at highBound
  have firstBound := apWeightedCollarIntegral (grade := grade) (order := 1) L sigma gamma ell cell field gradePositive
  have angularBound := (collar_angularJet_integral_le grade actual smooth).trans highBound
  have radialLow : scaledCellWeight L ell cell ^ (2 * (grade - 1)) *
      collarIntegral (fun point => ‖radialField actual point‖ ^ 2) ≤
        ((4 / 3 : ℝ) * collarOrderConstant 1) *
          ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
    have lowComparison := collar_radialAngularJet_integral_le 0 actual smooth
    simp only [angularJet_zero] at lowComparison
    exact (mul_le_mul_of_nonneg_left lowComparison (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)).trans firstBound
  have radialHigh : collarIntegral (fun point => ‖angularJet (grade - 1) (radialField actual) point‖ ^ 2) ≤
      ((4 / 3 : ℝ) * collarOrderConstant grade) *
        ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
    have highComparison := collar_radialAngularJet_integral_le (grade - 1) actual smooth
    rw [Nat.sub_add_cancel gradePositive] at highComparison
    exact highComparison.trans highBound
  have aggregate := add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add zeroBound angularBound) (frequencyGradeConstant_nonnegative grade))
    (mul_le_mul_of_nonneg_left (add_le_add radialLow radialHigh) (frequencyGradeConstant_nonnegative (grade - 1)))
  have final := preliminary.trans aggregate
  simp only [actual, collarField_boundary_coefficient] at final
  apply final.trans_eq
  unfold traceCellConstant
  ring

end Grad.GaugeCoefficients.Physical.WeightedTrace
