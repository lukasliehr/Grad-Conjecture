import AKAY26GenuineEmbeddedRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges
open Grad.Constraints Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

/-- SAME actual variable-coefficient tensor before the physical scalar cutoff. -/
def startupGenuinePrincipalTensorKernel (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) : StartupL2 3 →L[ℂ] StartupL2 3 :=
  ∑ row : Fin 3, (startupPrincipalFixedKernel outer inner row).comp
    (startupGenuineERKernelRow admissible data coherent inverseCoherent row)

def startupGenuinePrincipalTensorFirst (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) : StartupFirst 3 →L[ℂ] StartupFirst 3 :=
  ∑ row : Fin 3, (startupPrincipalFixedFirst outer inner row).comp
    (startupGenuineERFirstRow admissible data coherent inverseCoherent row)

theorem startupGenuinePrincipalTensor_compatible (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (outer inner : Fin 2) :
    StartupCompatible (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner)
      (startupGenuinePrincipalTensorFirst admissible data coherent inverseCoherent outer inner) :=
  startupCompatible_sum
    (fun row : Fin 3 => (startupPrincipalFixedKernel outer inner row).comp
      (startupGenuineERKernelRow admissible data coherent inverseCoherent row))
    (fun row : Fin 3 => (startupPrincipalFixedFirst outer inner row).comp
      (startupGenuineERFirstRow admissible data coherent inverseCoherent row))
    (fun row : Fin 3 => startupCompatible_comp (startupPrincipalFixed_compatible outer inner row)
      (startupGenuineERRow_compatible admissible data coherent inverseCoherent row))

/-- Quantitative smallness of the SAME four actual ER11 tensor entries,
 on both L2 and the genuine first graph, at unchanged analytic width. -/
theorem startupGenuinePrincipalTensor_bounds {parameters : PhaseParameters}
    {L ell rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ) (small : ActualGenuineStartupRowsSmall ledger inverseCoherent threshold)
    (outer inner : Fin 2) :
    ‖startupGenuinePrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent outer inner‖ ≤
        3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold) ∧
    ‖startupGenuinePrincipalTensorFirst admissible ledger.val ledger.property.1 inverseCoherent outer inner‖ ≤
        3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold) := by
  have rows := startupGenuineERRowsSmall ledger inverseCoherent threshold small
  constructor
  · exact startupFiniteComposedBound (startupPrincipalFixedKernel outer inner)
      (startupGenuineERKernelRow admissible ledger.val ledger.property.1 inverseCoherent)
      startupPrincipalFixedConstant (startupEREmbeddingConstant * threshold)
      startupPrincipalFixedConstant_positive.le (fun row => (startupPrincipalFixed_bounds outer inner row).1)
      (fun row => (rows row).1.le)
  · exact startupFiniteComposedBound (startupPrincipalFixedFirst outer inner)
      (startupGenuineERFirstRow admissible ledger.val ledger.property.1 inverseCoherent)
      startupPrincipalFixedConstant (startupEREmbeddingConstant * threshold)
      startupPrincipalFixedConstant_positive.le (fun row => (startupPrincipalFixed_bounds outer inner row).2)
      (fun row => (rows row).2.le)

end Grad.CartesianStartup
