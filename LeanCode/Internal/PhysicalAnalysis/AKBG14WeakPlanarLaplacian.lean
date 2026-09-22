import AKBG13WeakPlanarCurlRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- The genuine distributional Cartesian div-curl identity on arbitrary rough fields. -/
theorem startupWeakLaplacian_div_curl (vector : StartupL2 2) (cell : ℤ)
    (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) vector =
      if coordinate = 0 then
        -startupWeakDivergencePairing vector cell (startupDerivativeTest 0 test) +
          startupWeakCurlPairing vector cell (startupDerivativeTest 1 test)
      else -startupWeakDivergencePairing vector cell (startupDerivativeTest 1 test) -
          startupWeakCurlPairing vector cell (startupDerivativeTest 0 test) := by
  simp only [startupLaplacianTest, startupCoordinateTestPairing_add, add_apply,
    startupWeakDivergencePairing, startupWeakCurlPairing]
  rw [startupDerivativeTest_commute 1 0 test]
  fin_cases coordinate <;> norm_num <;> ring

/-- Second-order planar equation derived from the actual first-order weak force.
The unknown remains the SAME rough vector and no H1 premise is used. -/
theorem startupSame_planar_laplacian (theta : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation theta vector right)
    (curlMean : ∀ cell test, startupWeakCurlPairing vector cell (startupMeanTest test) = 0)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) vector =
      if coordinate = 0 then
        -startupWeakDivergencePairing vector cell (startupDerivativeTest 0 test) -
          startupWeakCurlPairing right cell (startupTrueInverseTest (startupDerivativeTest 1 test)) -
          (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 1 test))
      else -startupWeakDivergencePairing vector cell (startupDerivativeTest 1 test) +
          startupWeakCurlPairing right cell (startupTrueInverseTest (startupDerivativeTest 0 test)) +
          (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 0 test)) := by
  rw [startupWeakLaplacian_div_curl]
  simp_rw [startupSame_force_curl_inverse theta vector right equation curlMean]
  fin_cases coordinate <;> norm_num <;> ring

/-- The third Laplacian uses the recovered L2 gradient of the SAME Theta,
so its axial term is only one spatial derivative of an actual rough carrier. -/
theorem startupSame_third_laplacian (axial : ℤ → ℂ) (theta scalar source : StartupL2 1)
    (vector right : StartupL2 2)
    (forceEquation : StartupWeakForceEquation theta vector right)
    (thirdEquation : StartupWeakThirdEquation axial theta scalar source)
    (thetaMean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) theta = 0)
    (scalarMean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) scalar = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 (startupLaplacianTest test) scalar =
      axial cell * startupWeakDivergencePairing (startupRecoveredGradient vector right) cell test +
        startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 source) := by
  rw [startupSame_third_recovery axial theta scalar source thirdEquation thetaMean scalarMean]
  congr 1
  congr 1
  rw [startupLaplacianTest, startupCoordinateTestPairing_add, add_apply]
  unfold startupWeakDivergencePairing
  rw [← startupSame_weakGradient theta vector right forceEquation thetaMean,
    ← startupSame_weakGradient theta vector right forceEquation thetaMean]
  ring

end Grad.CartesianStartup
