import AKAX12LiteralFluxTensorWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- Literal weak principal expression on the full three-component a,c,s rows.
 The scalar diagonal is written as Delta Z0 c; angular Laplacian commutation is separate. -/
def startupPrincipalWeakExpression (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (force scalar flux : StartupL2 3) : ℂ :=
  ∑ outer : Fin 2,
    ((startupTestPairing cell ((startupPlanarRotatedEntryMap outer 1).adjoint vector)
      (startupDerivativeTest 0 (startupTrueInverseTest (startupDerivativeTest outer test))) force -
    startupTestPairing cell ((startupPlanarRotatedEntryMap outer 0).adjoint vector)
      (startupDerivativeTest 1 (startupTrueInverseTest (startupDerivativeTest outer test))) force) +
    startupTestPairing cell vector
      (startupTrueInverseTest (startupDerivativeTest outer (startupDerivativeTest outer test))) scalar +
    ((∑ inner : Fin 2, startupTestPairing cell ((startupPlanarEntryMap outer inner).adjoint vector)
      (startupDerivativeTest inner (startupDerivativeTest outer test)) flux) -
    (2 : ℂ) • ∑ middle : Fin 2,
      startupTestPairing cell ((startupPlanarRotatedEntryMap outer middle).adjoint vector)
        (startupDerivativeTest middle (startupTrueInverseTest (startupDerivativeTest outer test))) flux))

theorem startupPrincipalRows_mixedWeak (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (rows : Fin 3 → StartupL2 3) :
    (∑ outer : Fin 2, ∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (∑ row : Fin 3, startupPrincipalFixedKernel outer inner row (rows row))) =
      startupPrincipalWeakExpression cell vector test (rows 0) (rows 1) (rows 2) := by
  unfold startupPrincipalWeakExpression
  apply Finset.sum_congr rfl
  intro outer _
  have split : (∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (∑ row : Fin 3, startupPrincipalFixedKernel outer inner row (rows row))) =
      (∑ inner : Fin 2, startupTestPairing cell vector
        (startupDerivativeTest inner (startupDerivativeTest outer test)) (startupPrincipalFixedKernel outer inner 0 (rows 0))) +
      (∑ inner : Fin 2, startupTestPairing cell vector
        (startupDerivativeTest inner (startupDerivativeTest outer test)) (startupPrincipalFixedKernel outer inner 1 (rows 1))) +
      (∑ inner : Fin 2, startupTestPairing cell vector
        (startupDerivativeTest inner (startupDerivativeTest outer test)) (startupPrincipalFixedKernel outer inner 2 (rows 2))) := by
    simp only [Fin.sum_univ_three, map_add, Finset.sum_add_distrib]
  rw [split, startupPrincipalForce_mixedWeak, startupPrincipalScalar_mixedWeak, startupPrincipalFlux_mixedWeak]

/-- The exact actual coefficient tensor used in the accepted contraction has this literal weak action.
 Every row is the SAME full original ledger action; there is no assumption of the desired weak PDE. -/
theorem startupActualPrincipalTensor_mixedWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (field : StartupL2 3) :
    (∑ outer : Fin 2, ∑ inner : Fin 2, startupTestPairing cell vector
      (startupDerivativeTest inner (startupDerivativeTest outer test))
      (startupActualPrincipalTensorKernel admissible data coherent inverseCoherent outer inner field)) =
      startupPrincipalWeakExpression cell vector test
        (startupERKernelRow admissible data coherent inverseCoherent 0 field)
        (startupERKernelRow admissible data coherent inverseCoherent 1 field)
        (startupERKernelRow admissible data coherent inverseCoherent 2 field) := by
  simp only [startupActualPrincipalTensorKernel, sum_apply, ContinuousLinearMap.comp_apply]
  exact startupPrincipalRows_mixedWeak cell vector test
    (fun row => startupERKernelRow admissible data coherent inverseCoherent row field)

end Grad.CartesianStartup
