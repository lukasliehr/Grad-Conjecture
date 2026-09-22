import AKAX16TrueInverseLaplacianWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- Literal ER11 weak action with the scalar row in its original Z0 Delta order.
 The a-row is the curl term; the s-row contains the complete Hodge divergence. -/
def startupPrincipalERWeakExpression (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (force scalar flux : StartupL2 3) : ℂ :=
  ∑ outer : Fin 2,
    ((startupTestPairing cell ((startupPlanarRotatedEntryMap outer 1).adjoint vector)
      (startupDerivativeTest 0 (startupTrueInverseTest (startupDerivativeTest outer test))) force -
    startupTestPairing cell ((startupPlanarRotatedEntryMap outer 0).adjoint vector)
      (startupDerivativeTest 1 (startupTrueInverseTest (startupDerivativeTest outer test))) force) +
    startupTestPairing cell vector
      (startupDerivativeTest outer (startupDerivativeTest outer (startupTrueInverseTest test))) scalar +
    ((∑ inner : Fin 2, startupTestPairing cell ((startupPlanarEntryMap outer inner).adjoint vector)
      (startupDerivativeTest inner (startupDerivativeTest outer test)) flux) -
    (2 : ℂ) • ∑ middle : Fin 2,
      startupTestPairing cell ((startupPlanarRotatedEntryMap outer middle).adjoint vector)
        (startupDerivativeTest middle (startupTrueInverseTest (startupDerivativeTest outer test))) flux))

theorem startupPrincipalWeakExpression_eq_ER (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (force scalar flux : StartupL2 3) :
    startupPrincipalWeakExpression cell vector test force scalar flux =
      startupPrincipalERWeakExpression cell vector test force scalar flux := by
  unfold startupPrincipalWeakExpression startupPrincipalERWeakExpression
  simp only [Finset.sum_add_distrib]
  rw [startupTrueInverse_laplacianWeak]

/-- The SAME literal original coefficient tensor used in the accepted B10 contraction
 equals the ER11 principal expression against every genuine compact disk test,
 on the full integer-cell L2 carrier. No desired PDE or H1 regularity is assumed. -/
theorem startupActualPrincipalTensor_ERWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (field : StartupL2 3) :
    (∑ outer : Fin 2, ∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (startupActualPrincipalTensorKernel admissible data coherent inverseCoherent outer inner field)) =
      startupPrincipalERWeakExpression cell vector test
        (startupERKernelRow admissible data coherent inverseCoherent 0 field)
        (startupERKernelRow admissible data coherent inverseCoherent 1 field)
        (startupERKernelRow admissible data coherent inverseCoherent 2 field) :=
  (startupActualPrincipalTensor_mixedWeak admissible data coherent inverseCoherent cell vector test field).trans
    (startupPrincipalWeakExpression_eq_ER cell vector test _ _ _)

end Grad.CartesianStartup
