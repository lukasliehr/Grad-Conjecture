import GC18APProjection

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def apCoordinate {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) (index : DerivativeIndex grade) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] DiskL2 dimension :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : DerivativeIndex grade => DiskL2 dimension) index).comp
    ((lp.evalCLM ℂ (fun _ : ℤ => APRow dimension grade) 2 cell).comp (apGrade L sigma gamma ell dimension grade).subtypeL)

theorem apCoordinate_apply {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) (index : DerivativeIndex grade)
    (field : apGrade L sigma gamma ell dimension grade) : apCoordinate L sigma gamma ell cell index field = field.val cell index := rfl

def apUnscaledCoordinate {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) (index : DerivativeIndex grade) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] DiskL2 dimension :=
  ((scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index))⁻¹ • apCoordinate L sigma gamma ell cell index

theorem apUnscaledCoordinate_core {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (index : DerivativeIndex grade) (field : ℤ →₀ ClosedJet dimension) :
    apUnscaledCoordinate L sigma gamma ell cell index (apFiniteInto L sigma gamma ell field) =
      closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma ell cell (field cell)) := by
  change ((scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index))⁻¹ •
    (apFiniteEmbed L sigma gamma ell field cell index) = _
  rw [apFiniteEmbed_apply, apRowLinear_apply, smul_smul]
  have nonzero : (scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne')
  rw [inv_mul_cancel₀ nonzero, one_smul]

theorem apCoordinate_eq_scaled {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ) (index : DerivativeIndex grade)
    (field : apGrade L sigma gamma ell dimension grade) :
    field.val cell index = (scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index) •
      apUnscaledCoordinate L sigma gamma ell cell index field := by
  change _ = (scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index) •
    (((scaledCellWeight L ell cell : ℂ) ^ (grade - derivativeOrder index))⁻¹ • field.val cell index)
  rw [smul_smul, mul_inv_cancel₀, one_smul]
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne')

end Grad.GaugeCoefficients.Physical.RadialLedger
