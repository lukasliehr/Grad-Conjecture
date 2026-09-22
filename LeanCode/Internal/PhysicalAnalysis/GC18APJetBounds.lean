import GC18APOrthogonal
import ValueMapGrade

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Algebra

theorem apWeightedJet_valueMap {input output : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : ClosedJet input) :
    valueMapJet mapping (apWeightedJet sigma gamma ell cell field) =
      apWeightedJet sigma gamma ell cell (valueMapJet mapping field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value, apWeightedJet_value, apWeightedJet_value, valueMapJet_value]
  exact (mapping.restrictScalars ℝ).map_smul _ _

theorem apValueMap_coordinate_bound {input output grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : ClosedJet input)
    (index : DerivativeIndex grade) :
    ‖apRowLinear L sigma gamma ell cell (valueMapJet mapping field) index‖ ≤
      ‖mapping‖ * ‖apRowLinear L sigma gamma ell cell field index‖ := by
  rw [apRowLinear_apply, apRowLinear_apply, ← apWeightedJet_valueMap]
  change ‖(Grad.GaugeCoefficients.Envelope.scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index) •
    closedContinuousToDiskL2 (closedDerivative (valueMapJet mapping (apWeightedJet sigma gamma ell cell field))
      _ (cartesianMultiIndexWord (derivativeMultiIndex index)))‖ ≤ _
  rw [valueMapJet_derivative, norm_smul, norm_smul]
  calc
    _ ≤ ‖(Grad.GaugeCoefficients.Envelope.scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index)‖ *
        (‖mapping‖ * ‖closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell cell field)
          (derivativeMultiIndex index))‖) := mul_le_mul_of_nonneg_left (closedValueL2_valueMap_norm_le mapping _) (norm_nonneg _)
    _ = _ := mul_left_comm _ _ _

theorem apValueMap_row_bound {input output grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : ClosedJet input) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (valueMapJet mapping field)‖ ≤
      ‖mapping‖ * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (apValueMap_coordinate_bound L sigma gamma ell cell mapping field index) 2

def APJetBound {input output : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (mapping : ClosedJet input →ₗ[ℂ] ClosedJet output) (constant : ℝ) : Prop :=
  ∀ cell field, ‖apRowLinear (grade := grade) L sigma gamma ell cell (mapping field)‖ ≤
    constant * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖

theorem APJetBound.add {input output grade : ℕ} {L sigma gamma ell firstConstant secondConstant : ℝ}
    {first second : ClosedJet input →ₗ[ℂ] ClosedJet output}
    (firstBound : APJetBound L sigma gamma ell grade first firstConstant)
    (secondBound : APJetBound L sigma gamma ell grade second secondConstant) :
    APJetBound L sigma gamma ell grade (first + second) (firstConstant + secondConstant) := by
  intro cell field
  change ‖apRowLinear L sigma gamma ell cell (first field + second field)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans ((add_le_add (firstBound cell field) (secondBound cell field)).trans_eq (add_mul _ _ _).symm)

theorem APJetBound.sub {input output grade : ℕ} {L sigma gamma ell firstConstant secondConstant : ℝ}
    {first second : ClosedJet input →ₗ[ℂ] ClosedJet output}
    (firstBound : APJetBound L sigma gamma ell grade first firstConstant)
    (secondBound : APJetBound L sigma gamma ell grade second secondConstant) :
    APJetBound L sigma gamma ell grade (first - second) (firstConstant + secondConstant) := by
  intro cell field
  change ‖apRowLinear L sigma gamma ell cell (first field - second field)‖ ≤ _
  rw [map_sub]
  exact (norm_sub_le _ _).trans ((add_le_add (firstBound cell field) (secondBound cell field)).trans_eq (add_mul _ _ _).symm)

theorem APJetBound.comp {input middle output grade : ℕ} {L sigma gamma ell firstConstant secondConstant : ℝ}
    {first : ClosedJet middle →ₗ[ℂ] ClosedJet output} {second : ClosedJet input →ₗ[ℂ] ClosedJet middle}
    (firstBound : APJetBound L sigma gamma ell grade first firstConstant) (nonnegative : 0 ≤ firstConstant)
    (secondBound : APJetBound L sigma gamma ell grade second secondConstant) :
    APJetBound L sigma gamma ell grade (first.comp second) (firstConstant * secondConstant) := by
  intro cell field
  exact (firstBound cell (second field)).trans ((mul_le_mul_of_nonneg_left (secondBound cell field) nonnegative).trans_eq (mul_assoc _ _ _).symm)

theorem APJetBound.smul {input output grade : ℕ} {L sigma gamma ell constant : ℝ}
    {mapping : ClosedJet input →ₗ[ℂ] ClosedJet output} (bound : APJetBound L sigma gamma ell grade mapping constant) (scalar : ℂ) :
    APJetBound L sigma gamma ell grade (scalar • mapping) (‖scalar‖ * constant) := by
  intro cell field
  change ‖apRowLinear L sigma gamma ell cell (scalar • mapping field)‖ ≤ _
  rw [map_smul, norm_smul]
  exact (mul_le_mul_of_nonneg_left (bound cell field) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

end Grad.GaugeCoefficients.Physical.RadialLedger
