import GC14SeedExponential

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

def seedFourierLinear {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (inputDimension outputDimension : ℕ)
    (angle : ℝ) (point : ClosedDisk) :
    Coefficient L sigma gamma ell 0 inputDimension outputDimension →ₗ[ℂ]
      OperatorValue inputDimension outputDimension where
  toFun coefficient := fourierEvaluation coefficient angle point
  map_add' first second := by
    change (∑' cell : ℤ, fourierPhase cell angle •
      coefficientDerivative (first + second) cell zeroDerivativeIndex point) = _
    simp_rw [coefficientDerivative_add_apply, smul_add]
    exact (fourierTerm_summable admissible first angle point).tsum_add
      (fourierTerm_summable admissible second angle point)
  map_smul' scalar coefficient := by
    change (∑' cell : ℤ, fourierPhase cell angle •
      coefficientDerivative (scalar • coefficient) cell zeroDerivativeIndex point) = _
    simp_rw [coefficientDerivative_smul_apply, smul_comm (fourierPhase _ angle) scalar]
    exact (fourierTerm_summable admissible coefficient angle point).tsum_const_smul scalar

theorem seedFourier_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (angle : ℝ) (point : ClosedDisk) :
    ‖fourierEvaluation coefficient angle point‖ ≤ ‖coefficient‖ := by
  calc
    _ ≤ ∑' cell : ℤ, ‖fourierPhase cell angle • coefficientValue coefficient cell point‖ :=
      norm_tsum_le_tsum_norm (fourierTerm_norm_summable admissible coefficient angle point)
    _ = ∑' cell : ℤ, ‖coefficientValue coefficient cell point‖ := by
      simp_rw [norm_smul, fourierPhase_norm, one_mul]
    _ ≤ ∑' cell : ℤ, ‖weightedDerivative coefficient cell zeroDerivativeIndex‖ :=
      (coefficientValue_point_norm_summable admissible coefficient point).tsum_le_tsum
        (fun cell => coefficientValue_point_norm_le admissible coefficient cell point)
        (coordinate_norm_summable coefficient.val zeroDerivativeIndex)
    _ = _ := by
      rw [coefficient_norm_formula]
      simp only [derivativeIndex_zero_univ, Finset.sum_singleton]

def seedFourierCLM {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (inputDimension outputDimension : ℕ)
    (angle : ℝ) (point : ClosedDisk) :
    Coefficient L sigma gamma ell 0 inputDimension outputDimension →L[ℂ]
      OperatorValue inputDimension outputDimension :=
  (seedFourierLinear admissible inputDimension outputDimension angle point).mkContinuous 1
    (fun coefficient => by
      change ‖fourierEvaluation coefficient angle point‖ ≤ 1 * ‖coefficient‖
      rw [one_mul]
      exact seedFourier_norm_le admissible coefficient angle point)

theorem seedPower_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 dimension dimension)
    (power : ℕ) (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (gradedCoefficientPower admissible coefficient power) angle point =
      fourierEvaluation coefficient angle point ^ power := by
  induction power with
  | zero =>
    change fourierEvaluation (identityCoefficient L sigma gamma ell dimension) angle point = _
    rw [identityCoefficient_fourier, pow_zero]
    rfl
  | succ power inductionHypothesis =>
    rw [gradedCoefficientPower_succ, fourierComposition, inductionHypothesis, pow_succ']
    rfl

theorem seedExponential_fourier {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 dimension dimension)
    (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (seedCoefficientExponential admissible coefficient) angle point =
      NormedSpace.exp (fourierEvaluation coefficient angle point) := by
  change seedFourierCLM admissible dimension dimension angle point
      (∑' power : ℕ, seedExponentialTerm admissible coefficient power) = _
  rw [(seedFourierCLM admissible dimension dimension angle point).map_tsum
    (seedExponentialTerm_norm_summable admissible coefficient).of_norm]
  have each (power : ℕ) :
      seedFourierCLM admissible dimension dimension angle point
          (seedExponentialTerm admissible coefficient power) =
        ((power.factorial : ℂ)⁻¹) • fourierEvaluation coefficient angle point ^ power := by
    unfold seedExponentialTerm
    rw [map_smul]
    change ((power.factorial : ℂ)⁻¹) •
      fourierEvaluation (gradedCoefficientPower admissible coefficient power) angle point = _
    rw [seedPower_fourier]
  simp_rw [each]
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    (fourierEvaluation coefficient angle point)).tsum_eq

end Grad.GaugeCoefficients.Physical.Frame
