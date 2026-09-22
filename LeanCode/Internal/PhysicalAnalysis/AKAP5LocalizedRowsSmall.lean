import AKAP4OriginalEmbeddedRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000

open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

variable (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)

def startupCutoffConstant : ℝ :=
  1 + ‖startupCutoffL2 scalar smooth compact‖ + ‖startupCutoffFirst scalar smooth compact‖

theorem startupCutoffConstant_positive : 0 < startupCutoffConstant scalar smooth compact := by
  unfold startupCutoffConstant
  positivity

/-- The exact whole-plane cutoff of each literal a,c,s kernel has a
 compatible H1 operator. One fixed scalar payment makes BOTH norms small. -/
theorem startupActualLocalizedRowsSmall {parameters : PhaseParameters}
    {L ell rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    (included : tsupport scalar ⊆ openUnitDisk)
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ) (thresholdPositive : 0 < threshold)
    (small : ActualStartupRowsSmall ledger inverseCoherent
      (threshold / (startupCutoffConstant scalar smooth compact * startupEREmbeddingConstant + 1))) :
    ∀ row : Fin 3, ∃ regular : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (regular field) =
        startupLocalizedKernel scalar smooth compact
          (startupERKernelRow admissible ledger.val ledger.property.1 inverseCoherent row) (valueInclusion field)) ∧
      ‖startupLocalizedKernel scalar smooth compact
        (startupERKernelRow admissible ledger.val ledger.property.1 inverseCoherent row)‖ < threshold ∧
      ‖regular‖ < threshold := by
  have cutPositive := startupCutoffConstant_positive scalar smooth compact
  have embedPositive := startupEREmbeddingConstant_positive
  have productPositive := mul_pos cutPositive embedPositive
  have denominatorPositive : 0 < startupCutoffConstant scalar smooth compact * startupEREmbeddingConstant + 1 := by positivity
  have paid : startupCutoffConstant scalar smooth compact *
      (startupEREmbeddingConstant * (threshold /
        (startupCutoffConstant scalar smooth compact * startupEREmbeddingConstant + 1))) < threshold := by
    rw [← mul_assoc, ← mul_div_assoc]
    exact (div_lt_iff₀ denominatorPositive).mpr (by nlinarith)
  have coarseCut : ‖startupCutoffL2 scalar smooth compact‖ ≤ startupCutoffConstant scalar smooth compact := by
    unfold startupCutoffConstant
    linarith [norm_nonneg (startupCutoffFirst scalar smooth compact)]
  have fineCut : ‖startupCutoffFirst scalar smooth compact‖ ≤ startupCutoffConstant scalar smooth compact := by
    unfold startupCutoffConstant
    linarith [norm_nonneg (startupCutoffL2 scalar smooth compact)]
  intro row
  have rows := startupERRowsSmall ledger inverseCoherent _ small row
  obtain ⟨regular, same, regularBound⟩ := startupLocalizedKernel_h1_exists scalar smooth compact included
    (startupERKernelRow admissible ledger.val ledger.property.1 inverseCoherent row)
    (startupERFirstRow admissible ledger.val ledger.property.1 inverseCoherent row)
    (startupERRow_compatible admissible ledger.val ledger.property.1 inverseCoherent row)
  refine ⟨regular, same, ?_, ?_⟩
  · exact (startupLocalizedKernel_norm scalar smooth compact _).trans_lt
      ((mul_le_mul_of_nonneg_right coarseCut (norm_nonneg
        (startupERKernelRow admissible ledger.val ledger.property.1 inverseCoherent row))).trans_lt
        ((mul_lt_mul_of_pos_left rows.1 cutPositive).trans paid))
  · exact regularBound.trans_lt
      ((mul_le_mul_of_nonneg_right fineCut (norm_nonneg
        (startupERFirstRow admissible ledger.val ledger.property.1 inverseCoherent row))).trans_lt
        ((mul_lt_mul_of_pos_left rows.2 cutPositive).trans paid))

end Grad.CartesianStartup
