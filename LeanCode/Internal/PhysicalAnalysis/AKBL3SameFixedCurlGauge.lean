import AKBL2MeanReflectionTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

 theorem startupWeakCurl_quarter_divergence (vector : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing vector cell test =
      -startupWeakDivergencePairing (originalValueKernel quarterValueMap vector) cell test := by
  simp only [startupWeakCurlPairing, startupWeakDivergencePairing, startupCoordinateTestPairing_quarter]
  norm_num

 theorem startupWeakCurl_mean (vector : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing vector cell (startupMeanTest test) =
      startupWeakCurlPairing (originalAverageKernel vector) cell test := by
  rw [startupWeakCurl_quarter_divergence, startupWeakDivergence_mean, startupAverage_quarter,
    ← startupWeakCurl_quarter_divergence]

 theorem startupWeakCurl_reflection (vector : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing (startupPointKernel reflectionValueMap cartesianReflectionEquiv vector) cell test =
      -startupWeakCurlPairing vector cell (startupReflectionTest test) := by
  simp only [startupWeakCurlPairing, startupCoordinateTestPairing_reflection, startupDerivativeTest_reflection,
    startupCoordinateTestPairing_real_smul, smul_apply]
  norm_num
  ring

 theorem startupWeakCurl_sub_field (first second : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing (first - second) cell test =
      startupWeakCurlPairing first cell test - startupWeakCurlPairing second cell test := by
  simp only [startupWeakCurlPairing, map_sub]
  ring

 theorem startupWeakCurl_smul_field (scalar : ℂ) (vector : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing (scalar • vector) cell test = scalar * startupWeakCurlPairing vector cell test := by
  simp only [startupWeakCurlPairing, map_smul, smul_eq_mul]
  ring

/-- The literal tangential projection removes precisely the scalar mean of
curl, proved distributionally before any Cartesian H1 is available. -/
theorem startupTangential_curl_mean (vector : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing (originalTangentialKernel vector) cell (startupMeanTest test) =
      startupWeakCurlPairing vector cell (startupMeanTest test) := by
  change startupWeakCurlPairing ((1/2 : ℂ) • (originalAverageKernel vector -
    startupPointKernel reflectionValueMap cartesianReflectionEquiv (originalAverageKernel vector))) cell
    (startupMeanTest test) = _
  rw [startupWeakCurl_smul_field, startupWeakCurl_sub_field, startupWeakCurl_reflection,
    startupReflection_meanTest, ← startupWeakCurl_mean, startupMeanTest_idempotent]
  ring

 theorem startupSame_fixedPlanar_curlMean (vector : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing (vector - originalTangentialKernel vector) cell (startupMeanTest test) = 0 := by
  rw [startupWeakCurl_sub_field, startupTangential_curl_mean, sub_self]

 theorem startupSame_fullCircle_curlMean (covariant : StartupL2 3) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakCurlPairing (originalValueKernel planarPartMap (originalCircleKernel covariant)) cell
      (startupMeanTest test) = 0 := by
  rw [startupFullCircle_planar]
  exact startupSame_fixedPlanar_curlMean _ cell test

end Grad.CartesianStartup
