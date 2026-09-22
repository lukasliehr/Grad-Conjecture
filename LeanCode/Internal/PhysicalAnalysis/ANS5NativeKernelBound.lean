import ANS4KernelL2

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped BigOperators Interval ContDiff Topology
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

theorem apWeightedJet_kernelRotation {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ) (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight) (field : ClosedJet dimension) :
    kernelRotationJet weight weightSmooth (apWeightedJet sigma gamma ell cell field) =
      apWeightedJet sigma gamma ell cell (kernelRotationJet weight weightSmooth field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [kernelRotationJet_value, apWeightedJet_value, kernelRotationJet_value]
  have integrand (angle : ℝ) : weight angle •
      (apWeightedJet sigma gamma ell cell field).value (rotatedPoint angle point) =
      originalWeight sigma gamma ell cell point.val • (weight angle • field.value (rotatedPoint angle point)) := by
    rw [apWeightedJet_value]
    have weightEquality : originalWeight sigma gamma ell cell (rotatedPoint angle point).val =
        originalWeight sigma gamma ell cell point.val := apWeight_orthogonal sigma gamma ell cell (planeRotationEquiv angle) point.val
    rw [weightEquality]
    exact smul_comm _ _ _
  simp_rw [integrand]
  rw [integral_smul]
  exact smul_comm _ _ _

theorem apKernel_coordinate_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (M : ℝ) (nonnegative : 0 ≤ M) (weightBound : ∀ angle ∈ Icc (0 : ℝ) (2 * Real.pi), ‖weight angle‖ ≤ M)
    (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    ‖apRowLinear L sigma gamma ell cell (kernelRotationJet weight weightSmooth field) index‖ ≤
      M * ((2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖) := by
  let word : CartesianWord (derivativeOrder index) := cartesianMultiIndexWord (derivativeMultiIndex index)
  let scalar : ℂ := (scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index)
  let family : ℝ → C(ClosedDisk, ComplexEuclidean dimension) := fun angle =>
    scalar • kernelDerivativeFamily weight (apWeightedJet sigma gamma ell cell field) word angle
  have familyContinuous : Continuous family := (continuous_const (y := scalar)).smul
    (kernelDerivativeFamily_continuous weight weightSmooth (apWeightedJet sigma gamma ell cell field) word)
  have familyBound (angle : ℝ) (_inside : angle ∈ Icc (0 : ℝ) (2 * Real.pi)) :
      ‖closedContinuousToDiskL2 (family angle)‖ ≤ M * ((2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖) := by
    change ‖closedContinuousToDiskL2 (scalar • (weight angle •
      orthogonalDerivative (planeRotationEquiv angle) (apWeightedJet sigma gamma ell cell field) _ word))‖ ≤ _
    rw [closedContinuousToDiskL2_smul, closedContinuousToDiskL2_smul, norm_smul, norm_smul]
    have bound := apWeighted_orthogonal_word_bound L sigma gamma ell cell (planeRotationEquiv angle) field index.property word
    rw [← apWeightedJet_orthogonal] at bound
    change scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
      ‖closedContinuousToDiskL2 (closedDerivative (orthogonalJet (planeRotationEquiv angle)
        (apWeightedJet sigma gamma ell cell field)) (derivativeOrder index) word)‖ ≤ _ at bound
    rw [orthogonalJet_derivative] at bound
    have base : ‖scalar‖ * ‖closedContinuousToDiskL2
        (orthogonalDerivative (planeRotationEquiv angle) (apWeightedJet sigma gamma ell cell field) _ word)‖ ≤
        (2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
      simpa only [scalar, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (scaledCellWeight_nonnegative L ell cell)] using bound
    calc
      _ = ‖weight angle‖ * (‖scalar‖ * ‖closedContinuousToDiskL2
        (orthogonalDerivative (planeRotationEquiv angle) (apWeightedJet sigma gamma ell cell field) _ word)‖) := by ring
      _ ≤ M * ((2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖) :=
        mul_le_mul (weightBound angle _inside) base (by positivity) nonnegative
  have integralBound := closedValueL2_normalized_integral_norm_le familyContinuous familyBound
  rw [apRowLinear_apply, ← apWeightedJet_kernelRotation]
  change ‖scalar • closedContinuousToDiskL2 (closedDerivative
    (kernelRotationJet weight weightSmooth (apWeightedJet sigma gamma ell cell field)) _ word)‖ ≤ _
  rw [← closedContinuousToDiskL2_smul, kernelRotationJet_derivative_continuousMap]
  have equality : scalar • (((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      kernelDerivativeFamily weight (apWeightedJet sigma gamma ell cell field) word angle) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), family angle := by
    rw [smul_comm scalar ((2 * Real.pi)⁻¹ : ℝ), ← integral_smul]
  rw [equality]
  exact integralBound

theorem apKernel_row_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (M : ℝ) (nonnegative : 0 ≤ M) (weightBound : ∀ angle ∈ Icc (0 : ℝ) (2 * Real.pi), ‖weight angle‖ ≤ M) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (kernelRotationJet weight weightSmooth field)‖ ≤
      (M * orthogonalGradeConstant grade) * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have bound := apRow_norm_bound_of_coordinates _ (M * ((2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖))
    (mul_nonneg nonnegative (by positivity)) (apKernel_coordinate_bound L sigma gamma ell cell weight weightSmooth M nonnegative weightBound field)
  exact bound.trans_eq (by unfold orthogonalGradeConstant; ring)

end Grad.ActualAngularInverse
