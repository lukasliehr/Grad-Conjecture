import GQC26APValueMap

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Frame

def axialCore (L ell : ℝ) (dimension : ℕ) : (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] (ℤ →₀ ClosedJet dimension) where
  toFun core := Finsupp.onFinset core.support (fun cell => seedScaledFrequency L ell cell • core cell) (by
    intro cell nonzero
    apply Finsupp.mem_support_iff.mpr
    intro zero
    exact nonzero (by rw [zero, smul_zero]))
  map_add' first second := by
    apply Finsupp.ext
    intro cell
    change seedScaledFrequency L ell cell • (first cell + second cell) =
      seedScaledFrequency L ell cell • first cell + seedScaledFrequency L ell cell • second cell
    exact smul_add _ _ _
  map_smul' scalar core := by
    apply Finsupp.ext
    intro cell
    change seedScaledFrequency L ell cell • (scalar • core cell) = scalar • (seedScaledFrequency L ell cell • core cell)
    exact smul_comm _ _ _

theorem axialCore_apply (L ell : ℝ) (dimension : ℕ) (core : ℤ →₀ ClosedJet dimension) (cell : ℤ) :
    axialCore L ell dimension core cell = seedScaledFrequency L ell cell • core cell := rfl

theorem axialRow_coordinate_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (cell : ℤ) (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (seedScaledFrequency L ell cell • field) index‖ ≤
      ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell field‖ := by
  rw [map_smul]
  change ‖seedScaledFrequency L ell cell • (apRowLinear (grade := grade) L sigma gamma ell cell field index)‖ ≤ _
  rw [norm_smul, apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
  have power : 1 + (grade - derivativeOrder index) = grade + 1 - derivativeOrder index := by
    have := index.property
    change derivativeOrder index ≤ grade at this
    omega
  calc
    _ ≤ scaledCellWeight L ell cell * (scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
        ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma ell cell field)‖) :=
      mul_le_mul_of_nonneg_right (seedScaledFrequency_norm_le L ell cell)
        (mul_nonneg (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _) (norm_nonneg _))
    _ = scaledCellWeight L ell cell ^ (grade + 1 - derivativeOrder index) *
        ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma ell cell field)‖ := by
      rw [← power, pow_add, pow_one, mul_assoc]
    _ ≤ _ := apWeighted_word_bound L sigma gamma ell cell field (index.property.trans (Nat.le_succ grade))
      (cartesianMultiIndexWord (derivativeMultiIndex index))

theorem axialRow_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (cell : ℤ) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (seedScaledFrequency L ell cell • field)‖ ≤
      apLoweringConstant grade * ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell field‖ :=
  apRow_norm_bound_of_coordinates _ _ (norm_nonneg _) (axialRow_coordinate_bound L sigma gamma ell cell field)

theorem axialFinite_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (core : ℤ →₀ ClosedJet dimension) :
    ‖apFiniteInto (grade := grade) L sigma gamma ell (axialCore L ell dimension core)‖ ≤
      apLoweringConstant grade * ‖apFiniteInto (grade := grade + 1) L sigma gamma ell core‖ := by
  change ‖apFiniteEmbed (grade := grade) L sigma gamma ell (axialCore L ell dimension core)‖ ≤
    apLoweringConstant grade * ‖apFiniteEmbed (grade := grade + 1) L sigma gamma ell core‖
  calc
    _ ≤ ‖(apLoweringConstant grade : ℂ) • apFiniteEmbed (grade := grade + 1) L sigma gamma ell core‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      rw [apFiniteEmbed_apply, axialCore_apply]
      change _ ≤ ‖(apLoweringConstant grade : ℂ) • apFiniteEmbed (grade := grade + 1) L sigma gamma ell core cell‖
      rw [apFiniteEmbed_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (apLoweringConstant_nonnegative grade)]
      exact axialRow_bound L sigma gamma ell cell (core cell)
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (apLoweringConstant_nonnegative grade)]

end Grad.GaugeCoefficients.Physical.Compensated
