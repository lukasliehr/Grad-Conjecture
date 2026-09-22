import GC18APOrthogonal

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

theorem apWeightedJet_angular {dimension : ℕ} (sigma gamma ell : ℝ) (cell mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (apWeightedJet sigma gamma ell cell field) =
      apWeightedJet sigma gamma ell cell (angularClosedJet mode field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value, apWeightedJet_value, angularClosedJet_value]
  have integrand (angle : ℝ) : angularCharacter mode angle •
      (apWeightedJet sigma gamma ell cell field).value (rotatedPoint angle point) =
      originalWeight sigma gamma ell cell point.val • (angularCharacter mode angle • field.value (rotatedPoint angle point)) := by
    rw [apWeightedJet_value]
    have weightEquality : originalWeight sigma gamma ell cell (rotatedPoint angle point).val =
        originalWeight sigma gamma ell cell point.val := apWeight_orthogonal sigma gamma ell cell (planeRotationEquiv angle) point.val
    rw [weightEquality]
    exact smul_comm _ _ _
  simp_rw [integrand]
  rw [intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem apAngular_coordinate_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell mode : ℤ)
    (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    ‖apRowLinear L sigma gamma ell cell (angularClosedJet mode field) index‖ ≤
      (2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  let word : CartesianWord (derivativeOrder index) := cartesianMultiIndexWord (derivativeMultiIndex index)
  let scalar : ℂ := (scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index)
  let family : ℝ → C(ClosedDisk, ComplexEuclidean dimension) := fun angle =>
    scalar • angularDerivativeFamily mode (apWeightedJet sigma gamma ell cell field) word angle
  have familyContinuous : Continuous family := (continuous_const (y := scalar)).smul
    (angularDerivativeFamily_continuous mode (apWeightedJet sigma gamma ell cell field) word)
  have familyBound (angle : ℝ) (_inside : angle ∈ Icc (0 : ℝ) (2 * Real.pi)) :
      ‖closedContinuousToDiskL2 (family angle)‖ ≤ (2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
    change ‖closedContinuousToDiskL2 (scalar • (angularCharacter mode angle •
      orthogonalDerivative (planeRotationEquiv angle) (apWeightedJet sigma gamma ell cell field) _ word))‖ ≤ _
    rw [closedContinuousToDiskL2_smul, closedContinuousToDiskL2_smul, norm_smul, norm_smul,
      angularCharacter_norm, one_mul]
    have bound := apWeighted_orthogonal_word_bound L sigma gamma ell cell (planeRotationEquiv angle) field index.property word
    rw [← apWeightedJet_orthogonal] at bound
    change scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
      ‖closedContinuousToDiskL2 (closedDerivative (orthogonalJet (planeRotationEquiv angle)
        (apWeightedJet sigma gamma ell cell field)) (derivativeOrder index) word)‖ ≤ _ at bound
    rw [orthogonalJet_derivative] at bound
    simpa only [scalar, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (scaledCellWeight_nonnegative L ell cell)] using bound
  have integralBound := closedValueL2_normalized_integral_norm_le familyContinuous familyBound
  rw [apRowLinear_apply, ← apWeightedJet_angular]
  change ‖scalar • closedContinuousToDiskL2 (closedDerivative
    (angularClosedJet mode (apWeightedJet sigma gamma ell cell field)) _ word)‖ ≤ _
  rw [← closedContinuousToDiskL2_smul, angularClosedJet_derivative_continuousMap]
  have equality : scalar • (((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      angularDerivativeFamily mode (apWeightedJet sigma gamma ell cell field) word angle) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), family angle := by
    rw [smul_comm scalar ((2 * Real.pi)⁻¹ : ℝ), ← integral_smul]
  rw [equality]
  exact integralBound

theorem apAngular_row_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell mode : ℤ) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (angularClosedJet mode field)‖ ≤
      orthogonalGradeConstant grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have bound := apRow_norm_bound_of_coordinates _ ((2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖)
    (by positivity) (apAngular_coordinate_bound L sigma gamma ell cell mode field)
  exact bound.trans_eq (by unfold orthogonalGradeConstant; ring)

end Grad.GaugeCoefficients.Physical.RadialLedger
