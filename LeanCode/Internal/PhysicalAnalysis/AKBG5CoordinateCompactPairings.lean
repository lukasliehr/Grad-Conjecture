import AKBG4CovariantPrimitiveRotationTest

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier

def startupCoordinateTestPairing {dimension : ℕ} (cell : ℤ) (coordinate : Fin dimension)
    (test : TestFunction openUnitDisk) : StartupL2 dimension →L[ℂ] ℂ :=
  Grad.WeakTesting.compactPairing dimension openUnitDisk cell (EuclideanSpace.single coordinate 1)
    test.toFun test.smooth test.compact

theorem startupCoordinateTestPairing_apply {dimension : ℕ} (cell : ℤ) (coordinate : Fin dimension)
    (test : TestFunction openUnitDisk) (field : StartupL2 dimension) :
    startupCoordinateTestPairing cell coordinate test field =
      ∫ point in openUnitDisk, test.toFun point • field point cell coordinate := by
  change Grad.WeakTesting.compactPairing dimension openUnitDisk cell (EuclideanSpace.single coordinate 1)
    test.toFun test.smooth test.compact field = _
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
    Grad.WeakTesting.compactPairing_apply dimension openUnitDisk cell (EuclideanSpace.single coordinate 1)
      test.toFun test.smooth test.compact field

theorem startupCoordinateTestPairing_add {dimension : ℕ} (cell : ℤ) (coordinate : Fin dimension)
    (first second : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (startupAddTest first second) =
      startupCoordinateTestPairing cell coordinate first + startupCoordinateTestPairing cell coordinate second := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [add_apply, startupCoordinateTestPairing_apply]
  change (∫ point in openUnitDisk, (first.toFun point + second.toFun point) • field point cell coordinate) = _
  simp_rw [add_smul]
  exact integral_add (startupCoordinatePairing_integrable field cell coordinate first.toFun first.smooth first.compact)
    (startupCoordinatePairing_integrable field cell coordinate second.toFun second.smooth second.compact)

theorem startupCoordinateTestPairing_sub {dimension : ℕ} (cell : ℤ) (coordinate : Fin dimension)
    (first second : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (startupSubTest first second) =
      startupCoordinateTestPairing cell coordinate first - startupCoordinateTestPairing cell coordinate second := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [sub_apply, startupCoordinateTestPairing_apply]
  change (∫ point in openUnitDisk, (first.toFun point - second.toFun point) • field point cell coordinate) = _
  simp_rw [sub_smul]
  exact integral_sub (startupCoordinatePairing_integrable field cell coordinate first.toFun first.smooth first.compact)
    (startupCoordinatePairing_integrable field cell coordinate second.toFun second.smooth second.compact)

theorem startupCoordinateTestPairing_real_smul {dimension : ℕ} (cell : ℤ) (coordinate : Fin dimension)
    (scalar : ℝ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (multiplyTest (fun _ : Spatial => scalar) contDiff_const test) =
      scalar • startupCoordinateTestPairing cell coordinate test := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [smul_apply, startupCoordinateTestPairing_apply]
  change (∫ point in openUnitDisk, (scalar * test.toFun point) • field point cell coordinate) = _
  simp only [mul_smul]
  exact integral_smul scalar _

theorem startupCoordinateTestPairing_angular {dimension : ℕ} (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    (startupCoordinateTestPairing cell coordinate test).comp (startupRealAngularKernelDim dimension weight smooth) =
      startupCoordinateTestPairing cell coordinate (startupAngularCompactTest weight smooth test) := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [ContinuousLinearMap.comp_apply, startupCoordinateTestPairing_apply]
  change (∫ point in openUnitDisk, test.toFun point •
    (startupAngularKernel dimension (fun angle => (weight angle : ℂ)) (Complex.ofRealCLM.contDiff.comp smooth) field) point cell coordinate) =
    ∫ point in openUnitDisk, startupAngularTest weight test.toFun point • field point cell coordinate
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
    startupRealAngularKernel_transposeDim dimension weight smooth field cell (EuclideanSpace.single coordinate 1)
      test.toFun test.smooth test.compact

def startupCovariantCompactTest (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (source target : Fin 2) (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  startupAngularCompactTest (fun angle => weight angle * startupAverageWeight source target angle)
    (smooth.mul (startupAverageWeight_smooth source target)) test

theorem startupCoordinateTestPairing_covariant (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (cell : ℤ) (source : Fin 2) (test : TestFunction openUnitDisk) :
    (startupCoordinateTestPairing cell source test).comp (startupCovariantAngularKernel weight smooth) =
      ∑ target : Fin 2, startupCoordinateTestPairing cell target (startupCovariantCompactTest weight smooth source target test) := by
  apply ContinuousLinearMap.ext
  intro field
  simp only [ContinuousLinearMap.comp_apply, sum_apply, startupCoordinateTestPairing_apply]
  exact startupCovariantAngularKernel_transpose weight smooth field cell source test.toFun test.smooth test.compact

end Grad.CartesianStartup
