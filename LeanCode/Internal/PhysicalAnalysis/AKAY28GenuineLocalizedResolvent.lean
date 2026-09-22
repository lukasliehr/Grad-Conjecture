import AKAY27GenuinePrincipalTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

open MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

def startupGenuinePrincipalL2 (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation)) :
    FieldL2 →L[ℂ] FieldL2 :=
  startupSecondKernelSumFor (fun index : TensorIndex => startupLocalizedKernel scalar smooth compact
    (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent index.1 index.2))

/-- Actual bounded SAME H1 realization of the entire localized ER11
 principal tensor resolvent, with all four tensor entries paid. -/
theorem startupGenuinePrincipalH1_exists {parameters : PhaseParameters}
    {L ell rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (compact : HasCompactSupport scalar)
    (included : tsupport scalar ⊆ openUnitDisk)
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ) (small : ActualGenuineStartupRowsSmall ledger inverseCoherent threshold) :
    ∃ regular : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (regular field) = startupGenuinePrincipalL2 scalar smooth compact
        admissible ledger.val ledger.property.1 inverseCoherent (valueInclusion field)) ∧
      ‖startupGenuinePrincipalL2 scalar smooth compact admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
        4 * (startupCutoffConstant scalar smooth compact *
          (3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold))) ∧
      ‖regular‖ ≤ 4 * (startupCutoffConstant scalar smooth compact *
          (3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold))) := by
  classical
  let bound := 3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold)
  let payment := startupCutoffConstant scalar smooth compact * bound
  have cutNonnegative := (startupCutoffConstant_positive scalar smooth compact).le
  have coarseCut : ‖startupCutoffL2 scalar smooth compact‖ ≤ startupCutoffConstant scalar smooth compact := by
    unfold startupCutoffConstant
    linarith [norm_nonneg (startupCutoffFirst scalar smooth compact)]
  have fineCut : ‖startupCutoffFirst scalar smooth compact‖ ≤ startupCutoffConstant scalar smooth compact := by
    unfold startupCutoffConstant
    linarith [norm_nonneg (startupCutoffL2 scalar smooth compact)]
  have coarseBound (index : TensorIndex) :
      ‖startupLocalizedKernel scalar smooth compact
        (startupGenuinePrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)‖ ≤ payment :=
    (startupLocalizedKernel_norm scalar smooth compact _).trans (mul_le_mul coarseCut
      (startupGenuinePrincipalTensor_bounds ledger inverseCoherent threshold small index.1 index.2).1
      (norm_nonneg (startupGenuinePrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2))
      cutNonnegative)
  apply startupSecondKernelSum_h1_exists _ payment coarseBound
  intro index
  obtain ⟨regular, same, bounded⟩ := startupLocalizedKernel_h1_exists scalar smooth compact included
    (startupGenuinePrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)
    (startupGenuinePrincipalTensorFirst admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)
    (startupGenuinePrincipalTensor_compatible admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2)
  refine ⟨regular, same, bounded.trans ?_⟩
  exact mul_le_mul fineCut
    (startupGenuinePrincipalTensor_bounds ledger inverseCoherent threshold small index.1 index.2).2
    (norm_nonneg (startupGenuinePrincipalTensorFirst admissible ledger.val ledger.property.1 inverseCoherent index.1 index.2))
    cutNonnegative

end Grad.CartesianStartup
