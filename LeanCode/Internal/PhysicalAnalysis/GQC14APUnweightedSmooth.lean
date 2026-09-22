import GQC13APDerivativeCoordinates

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Envelope

def apInverseWeightedJet {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) : ClosedJet dimension :=
  smoothScalarWeightedJet (inverseWeight sigma gamma ell cell)
    ((smoothGoal sigma gamma ell cell).2.2) field

theorem apWeightedJet_inverse_left {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) :
    apWeightedJet sigma gamma ell cell (apInverseWeightedJet sigma gamma ell cell field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change physicalWeight sigma gamma ell cell point.val •
    (inverseWeight sigma gamma ell cell point.val • field.value point) = field.value point
  rw [smul_smul, (formulaGoal sigma gamma ell cell point.val).2.2.2.2, one_smul]

theorem apWeightedJet_inverse_right {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) :
    apInverseWeightedJet sigma gamma ell cell (apWeightedJet sigma gamma ell cell field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change inverseWeight sigma gamma ell cell point.val •
    (physicalWeight sigma gamma ell cell point.val • field.value point) = field.value point
  rw [smul_smul, mul_comm, (formulaGoal sigma gamma ell cell point.val).2.2.2.2, one_smul]

/-- The actual smooth closed Fourier coefficient belonging to an all-grade
AP2 element. The original smooth analytic weight is inverted literally. -/
def apFamilyJet {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family) (cell : ℤ) : ClosedJet dimension :=
  apInverseWeightedJet sigma gamma ell cell (apFamilyWeightedJet family coherent cell)

theorem apFamilyJet_weighted {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family) (cell : ℤ) :
    apWeightedJet sigma gamma ell cell (apFamilyJet family coherent cell) = apFamilyWeightedJet family coherent cell :=
  apWeightedJet_inverse_left sigma gamma ell cell _

/-- Every completed coordinate is the literal original AP2 weighted
derivative of the reconstructed closed jet, at every grade including zero. -/
theorem apFamilyJet_row {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family) (grade : ℕ) (cell : ℤ) :
    apRowLinear (grade := grade) L sigma gamma ell cell (apFamilyJet family coherent cell) = (family grade).val cell := by
  apply PiLp.ext
  intro index
  rw [apRowLinear_apply, apFamilyJet_weighted, apFamilyWeightedJet_l2,
    ← apCoordinate_eq_scaled]

theorem apFamilyJet_norm_sq {L sigma gamma ell : ℝ} {dimension : ℕ}
    (family : APFamily L sigma gamma ell dimension) (coherent : APFamilyCoherent family) (grade : ℕ) :
    ‖family grade‖ ^ 2 = ∑' cell : ℤ, ∑ index : DerivativeIndex grade,
      scaledCellWeight L ell cell ^ (2 * (grade - derivativeOrder index)) *
        ‖closedDerivativeL2 (derivativeMultiIndex index)
          (apWeightedJet sigma gamma ell cell (apFamilyJet family coherent cell))‖ ^ 2 := by
  rw [apGrade_norm_sq]
  apply tsum_congr
  intro cell
  rw [← apFamilyJet_row family coherent grade cell, ← PiLp.norm_sq_eq_of_L2, apRowLinear_norm_sq]

end Grad.GaugeCoefficients.Physical.Compensated
