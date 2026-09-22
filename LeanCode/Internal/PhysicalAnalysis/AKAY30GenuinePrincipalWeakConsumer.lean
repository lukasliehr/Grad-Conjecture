import AKAY29GenuineB10PrincipalContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- The exact actual coefficient tensor used in the accepted contraction has this literal weak action.
 Every row is the SAME full original ledger action; there is no assumption of the desired weak PDE. -/
theorem startupGenuinePrincipalTensor_mixedWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (field : StartupL2 3) :
    (∑ outer : Fin 2, ∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner field)) =
      startupPrincipalWeakExpression cell vector test
        (startupGenuineERKernelRow admissible data coherent inverseCoherent 0 field)
        (startupGenuineERKernelRow admissible data coherent inverseCoherent 1 field)
        (startupGenuineERKernelRow admissible data coherent inverseCoherent 2 field) := by
  simp only [startupGenuinePrincipalTensorKernel, sum_apply, ContinuousLinearMap.comp_apply]
  exact startupPrincipalRows_mixedWeak cell vector test
    (fun row => startupGenuineERKernelRow admissible data coherent inverseCoherent row field)

/-- The SAME literal original coefficient tensor used in the accepted B10 contraction
 equals the ER11 principal expression against every genuine compact disk test,
 on the full integer-cell L2 carrier. No desired PDE or H1 regularity is assumed. -/
theorem startupGenuinePrincipalTensor_ERWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (field : StartupL2 3) :
    (∑ outer : Fin 2, ∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (startupGenuinePrincipalTensorKernel admissible data coherent inverseCoherent outer inner field)) =
      startupPrincipalERWeakExpression cell vector test
        (startupGenuineERKernelRow admissible data coherent inverseCoherent 0 field)
        (startupGenuineERKernelRow admissible data coherent inverseCoherent 1 field)
        (startupGenuineERKernelRow admissible data coherent inverseCoherent 2 field) :=
  (startupGenuinePrincipalTensor_mixedWeak admissible data coherent inverseCoherent cell vector test field).trans
    (startupPrincipalWeakExpression_eq_ER cell vector test _ _ _)

end Grad.CartesianStartup
