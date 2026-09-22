import AKBN8RawProjectedForceConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupMeanFree_scalar_pairing (field : StartupL2 1) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 test (field - startupRealAngularKernelDim 1 (fun _ => 1) contDiff_const field) =
      startupCoordinateTestPairing cell 0 (startupMeanFreeTest test) field := by
  have mean := congrArg (fun map : StartupL2 1 →L[ℂ] ℂ => map field)
    (startupCoordinateTestPairing_angular (fun _ => 1) contDiff_const cell 0 test)
  change startupCoordinateTestPairing cell 0 test (startupRealAngularKernelDim 1 (fun _ => 1) contDiff_const field) =
    startupCoordinateTestPairing cell 0 (startupMeanTest test) field at mean
  rw [map_sub,mean]
  exact (congrArg (fun map : StartupL2 1 →L[ℂ] ℂ => map field)
    (startupCoordinateTestPairing_sub cell 0 test (startupMeanTest test))).symm

theorem startupMeanFree_divergence_pairing (field : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (field - originalAverageKernel field) cell test =
      startupWeakDivergencePairing field cell (startupMeanFreeTest test) := by
  have mean := startupWeakDivergence_mean field cell test
  unfold startupWeakDivergencePairing at mean ⊢
  simp only [startupMeanFreeTest,startupDerivativeTest_sub,startupCoordinateTestPairing_sub,sub_apply,map_sub]
  linear_combination mean

/-- The actual cofactor is -a_C+h. Its outer scalar P0 becomes exactly
(I-A)h_planar and (I-Pi)h_scalar; no source or axial projection is dropped. -/
theorem startupDeterminantEquation_of_balance (axial : ℤ → ℂ)
    (vector cofactorVector : StartupL2 2) (scalar cofactorScalar determinant : StartupL2 1)
    (balance : ∀ cell test, startupCoordinateTestPairing cell 0 test determinant =
      startupWeakDivergencePairing cofactorVector cell (startupMeanFreeTest test) +
        axial cell * startupCoordinateTestPairing cell 0 (startupMeanFreeTest test) cofactorScalar) :
    StartupWeakDeterminantEquation axial vector scalar determinant
      ((cofactorVector + vector) - originalAverageKernel (cofactorVector + vector))
      ((cofactorScalar + scalar) - startupRealAngularKernelDim 1 (fun _ => 1) contDiff_const (cofactorScalar + scalar)) := by
  intro cell test
  rw [startupMeanFree_divergence_pairing,startupMeanFree_scalar_pairing,balance]
  simp only [startupWeakDivergencePairing,map_add]
  ring

end Grad.CartesianStartup
