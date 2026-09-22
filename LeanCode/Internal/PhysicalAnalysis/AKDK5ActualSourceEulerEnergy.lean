import AKDK4FiniteEulerEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.OriginalCartesianTameEstimate Grad.AnnularGeneralSourceRegularity
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.NonlinearProduct

def originalEulerCurveConstant (lower : ℝ) (power : ℕ) (rank : ℕ) : ℝ :=
  Nat.casesOn rank (lower⁻¹*Real.sqrt (restrictionRowConstant power 0))
    (fun order => rawEulerEnergyPayment (fun raw => lower⁻¹*Real.sqrt (restrictionRowConstant power raw)) (positiveEulerTerms order))

theorem originalEulerCurveConstant_nonnegative (lower : ℝ) (positive : 0<lower) (power rank : ℕ) :
    0≤originalEulerCurveConstant lower power rank := by
  cases rank with
  | zero => exact mul_nonneg (inv_nonneg.mpr positive.le) (Real.sqrt_nonneg _)
  | succ rank => exact rawEulerEnergyPayment_nonnegative _ (fun raw => mul_nonneg (inv_nonneg.mpr positive.le) (Real.sqrt_nonneg _)) _

/-- Every mixed Euler/tangential derivative of the SAME original weighted
Cartesian source is quantitatively paid at its total original grade. -/
theorem actualCartesianCurve_eulerCollarEnergy {dimension grade power rank : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (paid : power+rank≤grade) (field : ACore parameters dimension) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
        (cartesianWeightedRadialCurve parameters lower positive bounded field power 0) radius‖^2)) ≤
      ENNReal.ofReal ((originalEulerCurveConstant lower power rank*originalGradeNorm grade field)^2) := by
  let jets := cartesianWeightedRadialCurve parameters lower positive bounded field power
  have fidelity := actualRawEulerJets_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun radius inside => (positive.trans_le inside.1).ne') jets
    (fun raw radius inside => cartesianWeightedRadialCurve_derivative parameters lower positive bounded field power raw radius inside) rank
  have same : (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank (jets 0) radius‖^2)) =
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖actualRawEulerJets jets rank radius‖^2)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    rw [fidelity inside]
  rw [same]
  cases rank with
  | zero => exact actualCartesianCurve_mixedCollarEnergy parameters lower positive bounded paid field
  | succ rank =>
      change (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖rawEulerPolynomial jets (positiveEulerTerms rank) radius‖^2)) ≤ _
      apply rawEulerPolynomial_squareEnergy lower positive jets
        (fun raw => cartesianWeightedRadialCurve_continuous parameters lower positive bounded field power raw)
        (fun raw => lower⁻¹*Real.sqrt (restrictionRowConstant power raw))
        (fun raw => mul_nonneg (inv_nonneg.mpr positive.le) (Real.sqrt_nonneg _))
        (originalGradeNorm grade field) (originalGradeNorm_nonnegative _ _) (positiveEulerTerms rank)
      intro term member
      have rankBound := positiveEulerTerms_rank rank term member
      exact actualCartesianCurve_mixedCollarEnergy parameters lower positive bounded (by omega) field

end Grad.OriginalTerminalAllocation
