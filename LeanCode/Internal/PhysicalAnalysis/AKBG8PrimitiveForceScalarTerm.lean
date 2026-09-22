import AKBG7ActualCovariantMeanIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- Exact scalar part of the genuine force after C. Only the true scalar
mean gauge is used; no regularity of Theta is assumed. -/
theorem startupCovariantPrimitive_theta_term (theta : StartupL2 1)
    (mean : ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
      startupCoordinateTestPairing cell 0 (startupMeanTest test) theta = 0)
    (cell : ℤ) (source : Fin 2) (test : TestFunction openUnitDisk) :
    (∑ target : Fin 2, startupCoordinateTestPairing cell 0
      (startupRotationTest (startupDerivativeTest target
        (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source target test))) theta) =
        -startupCoordinateTestPairing cell 0 (startupDerivativeTest source test) theta := by
  rw [Fin.sum_univ_two, ← add_apply, ← startupCoordinateTestPairing_add,
    startupCovariantPrimitiveCompact_gradientRotation, startupCoordinateTestPairing_sub, sub_apply,
    mean cell (startupDerivativeTest source test), zero_sub]

theorem startupCoordinateTestPairing_quarter (field : StartupL2 2) (cell : ℤ) (coordinate : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (originalValueKernel quarterValueMap field) =
      if coordinate = 0 then -startupCoordinateTestPairing cell 1 test field
      else startupCoordinateTestPairing cell 0 test field := by
  rw [startupCoordinateTestPairing_apply, startupCoordinateTestPairing_apply, startupCoordinateTestPairing_apply]
  exact startupQuarterKernel_pairing field cell coordinate test.toFun

theorem startupCovariantPrimitive_pairing (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell source test (startupCovariantPrimitiveKernel field) =
      ∑ target : Fin 2, startupCoordinateTestPairing cell target
        (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source target test) field := by
  exact congrArg (fun operator : StartupL2 2 →L[ℂ] ℂ => operator field)
    (startupCoordinateTestPairing_covariant (fun angle : ℝ => angle) contDiff_id cell source test)

theorem startupAverage_pairing (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell source test (originalAverageKernel field) =
      ∑ target : Fin 2, startupCoordinateTestPairing cell target
        (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test) field := by
  rw [← startupCovariantAngularKernel_one]
  exact congrArg (fun operator : StartupL2 2 →L[ℂ] ℂ => operator field)
    (startupCoordinateTestPairing_covariant (fun _ : ℝ => 1) contDiff_const cell source test)

end Grad.CartesianStartup
