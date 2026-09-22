import AKBG25SameFullCircleForceConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.ActualAngularInverse

theorem startupAngularTest_zero (weight : ℝ → ℝ) (point : Spatial) :
    startupAngularTest weight (fun _ : Spatial => (0 : ℝ)) point = 0 := by
  simp only [startupAngularTest, mul_zero, integral_zero]

/-- Idempotence of the literal angular mean follows from the already checked
full-period fundamental theorem and its vanishing rotational derivative. -/
theorem startupMeanTest_idempotent (test : TestFunction openUnitDisk) :
    startupMeanTest (startupMeanTest test) = startupMeanTest test := by
  have rotationZero : startupRotationDerivative (startupAngularTest (fun _ : ℝ => 1) test.toFun) =
      fun _ : Spatial => (0 : ℝ) := by
    funext point
    rw [startupAngularTest_rotation (fun _ : ℝ => 1) contDiff_const test.toFun test.smooth,
      startupMeanTest_rotation_zero test.toFun test.smooth]
  apply startupTest_ext
  intro point
  have fundamental := startupPrimitiveTest_rotation (startupAngularTest (fun _ : ℝ => 1) test.toFun)
    (startupAngularTest_smooth _ contDiff_const test.toFun test.smooth) point
  rw [rotationZero, startupAngularTest_zero] at fundamental
  exact sub_eq_zero.mp fundamental.symm

theorem startupZeroMean_realDim (dimension : ℕ) :
    startupCharacterKernel dimension 0 = startupRealAngularKernelDim dimension (fun _ : ℝ => 1) contDiff_const := by
  unfold startupCharacterKernel startupRealAngularKernelDim
  congr 1
  funext angle
  simp only [angularCharacter_zero_mode, Complex.ofReal_one]

/-- The literal fixed quotient's scalar gauge on every rough L2 field,
without any original physical gauge or smoothness assumption. -/
theorem startupSame_fixedScalar_mean (scalar : StartupL2 1) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 (startupMeanTest test)
      (scalar - startupCharacterKernel 1 0 scalar) = 0 := by
  rw [map_sub, startupZeroMean_realDim]
  have transpose := congrArg (fun operator : StartupL2 1 →L[ℂ] ℂ => operator scalar)
    (startupCoordinateTestPairing_angular (fun _ : ℝ => 1) contDiff_const cell 0 (startupMeanTest test))
  change startupCoordinateTestPairing cell 0 (startupMeanTest test)
    (startupRealAngularKernelDim 1 (fun _ : ℝ => 1) contDiff_const scalar) =
    startupCoordinateTestPairing cell 0 (startupMeanTest (startupMeanTest test)) scalar at transpose
  rw [transpose, startupMeanTest_idempotent, sub_self]

theorem startupSame_fullCircle_scalarMean (covariant : StartupL2 3) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 (startupMeanTest test)
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) = 0 := by
  rw [startupFullCircle_scalar]
  exact startupSame_fixedScalar_mean _ cell test

end Grad.CartesianStartup
