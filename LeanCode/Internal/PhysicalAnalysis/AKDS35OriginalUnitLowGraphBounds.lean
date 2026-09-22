import AKDS33OriginalUnitPrincipalEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients Grad.CartesianStartup
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger
variable {parameters : PhaseParameters} {length radius : ℝ}

/-- Uniform low graph bounds for the faithful original-L gauge and its
complement extension. The fixed constants contain no running rank. -/
theorem gauge_extension_bounds (radiusNonnegative : 0≤radius) (state : OriginalUnitRankState parameters length radius) :
    (‖originalMatrixKernel (unitDiskAdmissible parameters) (fullGaugeFamily state.data.gaugeDeviation)
      (fullGaugeFamily_coherent _ (state.coherent radiusNonnegative).2.2.2.1)‖≤
      startupGaugeMatrixConstant 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) ∧
    ‖startupMatrixFirstGraphCLM (unitDiskAdmissible parameters) (fullGaugeFamily state.data.gaugeDeviation)
      (fullGaugeFamily_coherent _ (state.coherent radiusNonnegative).2.2.2.1)‖≤
      startupGaugeMatrixConstant 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius)) ∧
    (‖originalMatrixKernel (unitDiskAdmissible parameters)
      (complementExtensionFamily (unitDiskAdmissible parameters) state.data.gaugeDeviation)
      (complementExtensionFamily_coherent _ _ (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative))‖≤
      startupExtensionMatrixConstant 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius) ∧
    ‖startupMatrixFirstGraphCLM (unitDiskAdmissible parameters)
      (complementExtensionFamily (unitDiskAdmissible parameters) state.data.gaugeDeviation)
      (complementExtensionFamily_coherent _ _ (state.coherent radiusNonnegative).2.2.2.1 (state.inverseCoherent radiusNonnegative))‖≤
      startupExtensionMatrixConstant 1 parameters.sigma0 parameters.gamma (originalUnitFour parameters length radius)) := by
  let L : ℝ := 1
  let ell : ℝ := 1
  let admissible := unitDiskAdmissible parameters
  let base := state.field
  let rho := state.rho
  let epsilon := state.epsilon
  let four := originalUnitFour parameters length radius
  have fourNonnegative := originalUnitFour_nonnegative parameters length radius
  have unit := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 10≤12)).trans state.unit
  have small := state.determinantLow
  have inverseCoherent := state.inverseCoherent radiusNonnegative
  have gaugeBound (grade : ℕ) := (state.rowBounds radiusNonnegative grade).1
  have low := (physicalBudget_monotone parameters base rho epsilon (by norm_num : 6 ≤ 10)).trans unit
  have gaugeUnit (grade : ℕ) (ordered : grade ≤ 1) : ‖state.data.gaugeDeviation grade‖ ≤ four grade := by
    exact (gaugeBound grade).trans ((mul_le_mul_of_nonneg_left
      ((physicalBudget_monotone parameters base rho epsilon (by omega : grade + 4 ≤ 10)).trans unit)
      (fourNonnegative grade)).trans_eq (mul_one _))
  have extensionUnit (grade : ℕ) (ordered : grade ≤ 1) :
      ‖complementExtensionFamily admissible state.data.gaugeDeviation grade‖ ≤
        (Fintype.card (DerivativeIndex grade) : ℝ) + complementExtensionConstant four grade := by
    apply (startupExtension_coefficient_bound admissible base state.data.gaugeDeviation
      (state.coherent radiusNonnegative).2.2.2.1 four fourNonnegative low gaugeBound small grade).trans
    have coeffPositive : 0 ≤ complementExtensionConstant four grade := abs_nonneg _
    exact add_le_add_right ((mul_le_mul_of_nonneg_left
      ((physicalBudget_monotone parameters base rho epsilon (by omega : grade + 6 ≤ 10)).trans unit)
      coeffPositive).trans_eq (mul_one _)) _
  exact ⟨startupMatrix_uniform_bound admissible _ _
      (startupFullGauge_coefficient_bound _ 0 (gaugeUnit 0 (by norm_num)))
      (startupFullGauge_coefficient_bound _ 1 (gaugeUnit 1 le_rfl)),
    startupMatrix_uniform_bound admissible _ _ (extensionUnit 0 (by norm_num)) (extensionUnit 1 le_rfl)⟩

end Grad.OriginalCoreRealization.OriginalUnitRankState
