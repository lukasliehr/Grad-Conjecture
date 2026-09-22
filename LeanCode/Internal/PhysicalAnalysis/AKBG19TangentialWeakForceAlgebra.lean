import AKBG18RoughRotationalResonance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier
open Grad.RepresentedKernel.SpatialProduct Grad.PhysicalFamily

 theorem startupRotationTest_const_mul (scalar : ℝ) (test : TestFunction openUnitDisk) :
    startupRotationTest (multiplyTest (fun _ : Spatial => scalar) contDiff_const test) =
      multiplyTest (fun _ : Spatial => scalar) contDiff_const (startupRotationTest test) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ ((fun _ : Spatial => scalar) * test.toFun) point (planeQuarterTurn point) =
    scalar * fderiv ℝ test.toFun point (planeQuarterTurn point)
  rw [fderiv_mul (differentiableAt_const scalar) (test.smooth.differentiable (by simp) point)]
  simp only [fderiv_const_apply, smul_zero, add_zero, smul_apply, smul_eq_mul]

 theorem startupDerivativeTest_const_mul (scalar : ℝ) (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupDerivativeTest direction (multiplyTest (fun _ : Spatial => scalar) contDiff_const test) =
      multiplyTest (fun _ : Spatial => scalar) contDiff_const (startupDerivativeTest direction test) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ ((fun _ : Spatial => scalar) * test.toFun) point (spatialDirection direction) =
    scalar * fderiv ℝ test.toFun point (spatialDirection direction)
  rw [fderiv_mul (differentiableAt_const scalar) (test.smooth.differentiable (by simp) point)]
  simp only [fderiv_const_apply, smul_zero, add_zero, smul_apply, smul_eq_mul]

 theorem startupTangential_rotation_pairing (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell source (startupRotationTest test) (originalTangentialKernel field) =
      -startupCoordinateTestPairing cell source test (originalValueKernel quarterValueMap (originalTangentialKernel field)) := by
  change startupCoordinateTestPairing cell source (startupRotationTest test)
    ((1/2 : ℂ) • (originalAverageKernel field - startupPointKernel reflectionValueMap cartesianReflectionEquiv
      (originalAverageKernel field))) = _
  change _ = -startupCoordinateTestPairing cell source test (originalValueKernel quarterValueMap
    ((1/2 : ℂ) • (originalAverageKernel field - startupPointKernel reflectionValueMap cartesianReflectionEquiv
      (originalAverageKernel field))))
  simp only [map_smul, map_sub, startupAverage_rotation_pairing, startupReflectedAverage_rotation_pairing, smul_eq_mul]
  ring

def startupWeakForceVectorPairing (vector : StartupL2 2) (cell : ℤ) (coordinate : Fin 2)
    (test : TestFunction openUnitDisk) : ℂ :=
  startupCoordinateTestPairing cell coordinate (startupRotationTest test) vector -
    startupCoordinateTestPairing cell coordinate test (originalValueKernel quarterValueMap vector)

 theorem startupWeakForceVector_add_test (vector : StartupL2 2) (cell : ℤ) (coordinate : Fin 2)
    (first second : TestFunction openUnitDisk) :
    startupWeakForceVectorPairing vector cell coordinate (startupAddTest first second) =
      startupWeakForceVectorPairing vector cell coordinate first + startupWeakForceVectorPairing vector cell coordinate second := by
  simp only [startupWeakForceVectorPairing, startupRotationTest_add, startupCoordinateTestPairing_add, add_apply]
  ring

 theorem startupWeakForceVector_sub_test (vector : StartupL2 2) (cell : ℤ) (coordinate : Fin 2)
    (first second : TestFunction openUnitDisk) :
    startupWeakForceVectorPairing vector cell coordinate (startupSubTest first second) =
      startupWeakForceVectorPairing vector cell coordinate first - startupWeakForceVectorPairing vector cell coordinate second := by
  simp only [startupWeakForceVectorPairing, startupRotationTest_sub, startupCoordinateTestPairing_sub, sub_apply]
  ring

 theorem startupWeakForceVector_const_mul_test (vector : StartupL2 2) (cell : ℤ) (coordinate : Fin 2)
    (scalar : ℝ) (test : TestFunction openUnitDisk) :
    startupWeakForceVectorPairing vector cell coordinate (multiplyTest (fun _ : Spatial => scalar) contDiff_const test) =
      (scalar : ℂ) * startupWeakForceVectorPairing vector cell coordinate test := by
  simp only [startupWeakForceVectorPairing, startupRotationTest_const_mul,
    startupCoordinateTestPairing_real_smul, smul_apply, Complex.real_smul]
  ring

 theorem startupWeakForceVector_fixed_quotient (vector : StartupL2 2) (cell : ℤ) (coordinate : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupWeakForceVectorPairing (vector - originalTangentialKernel vector) cell coordinate test =
      startupWeakForceVectorPairing vector cell coordinate test + (2 : ℂ) *
        startupCoordinateTestPairing cell coordinate test (originalValueKernel quarterValueMap (originalTangentialKernel vector)) := by
  simp only [startupWeakForceVectorPairing, map_sub, startupTangential_rotation_pairing]
  ring

end Grad.CartesianStartup
