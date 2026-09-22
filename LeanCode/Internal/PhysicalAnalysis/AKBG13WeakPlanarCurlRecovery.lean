import AKBG12RotationDerivativeCommutators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

def startupWeakDivergencePairing (vector : StartupL2 2) (cell : ℤ)
    (test : TestFunction openUnitDisk) : ℂ :=
  -startupCoordinateTestPairing cell 0 (startupDerivativeTest 0 test) vector -
    startupCoordinateTestPairing cell 1 (startupDerivativeTest 1 test) vector

def startupWeakCurlPairing (vector : StartupL2 2) (cell : ℤ)
    (test : TestFunction openUnitDisk) : ℂ :=
  startupCoordinateTestPairing cell 0 (startupDerivativeTest 1 test) vector -
    startupCoordinateTestPairing cell 1 (startupDerivativeTest 0 test) vector

theorem startupWeakCurl_sub (vector : StartupL2 2) (cell : ℤ)
    (first second : TestFunction openUnitDisk) :
    startupWeakCurlPairing vector cell (startupSubTest first second) =
      startupWeakCurlPairing vector cell first - startupWeakCurlPairing vector cell second := by
  simp only [startupWeakCurlPairing, startupDerivativeTest_sub,
    startupCoordinateTestPairing_sub, sub_apply]
  ring

/-- Curl of the genuine force equation in distributions. Both Cartesian
commutator contributions are present; their sum is twice the divergence. -/
theorem startupSame_force_curl (theta : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation theta vector right)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing vector cell (startupRotationTest test) =
      startupWeakCurlPairing right cell test + (2 : ℂ) * startupWeakDivergencePairing vector cell test := by
  have first := equation cell 0 (startupDerivativeTest 1 test)
  have second := equation cell 1 (startupDerivativeTest 0 test)
  rw [startupDerivativeTest_commute 1 0 test] at second
  rw [startupCoordinateTestPairing_quarter] at first second
  norm_num at first second
  have cancelled :
      startupCoordinateTestPairing cell 1 (startupDerivativeTest 0 test) right -
        startupCoordinateTestPairing cell 0 (startupDerivativeTest 1 test) right =
      startupCoordinateTestPairing cell 1 (startupRotationTest (startupDerivativeTest 0 test)) vector -
        startupCoordinateTestPairing cell 0 (startupRotationTest (startupDerivativeTest 1 test)) vector -
        startupCoordinateTestPairing cell 0 (startupDerivativeTest 0 test) vector -
        startupCoordinateTestPairing cell 1 (startupDerivativeTest 1 test) vector := by
    linear_combination second - first
  rw [startupRotationDerivativeTest_zero, startupRotationDerivativeTest_one,
    startupCoordinateTestPairing_sub, startupCoordinateTestPairing_add, sub_apply, add_apply] at cancelled
  unfold startupWeakCurlPairing startupWeakDivergencePairing
  linear_combination cancelled

/-- True angular inversion of the SAME distributional curl. Its actual
mean gauge is retained as a compact-test identity, with no curl-L2 premise. -/
theorem startupSame_force_curl_inverse (theta : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation theta vector right)
    (curlMean : ∀ cell test, startupWeakCurlPairing vector cell (startupMeanTest test) = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing vector cell test =
      -startupWeakCurlPairing right cell (startupTrueInverseTest test) -
        (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest test) := by
  have transformed := startupSame_force_curl theta vector right equation cell (startupTrueInverseTest test)
  rw [startupTrueInverseTest_rotation, startupWeakCurl_sub] at transformed
  change startupWeakCurlPairing vector cell (startupMeanTest test) - _ = _ at transformed
  rw [curlMean] at transformed
  linear_combination -transformed

end Grad.CartesianStartup
