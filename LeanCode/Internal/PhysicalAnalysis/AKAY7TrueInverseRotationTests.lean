import AKAY6AngularPrimitiveFundamental

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.PhysicalFamily Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupRotationTest_sub (first second : TestFunction openUnitDisk) :
    startupRotationTest (startupSubTest first second) =
      startupSubTest (startupRotationTest first) (startupRotationTest second) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ (first.toFun - second.toFun) point (planeQuarterTurn point) =
    fderiv ℝ first.toFun point (planeQuarterTurn point) -
      fderiv ℝ second.toFun point (planeQuarterTurn point)
  rw [fderiv_sub (first.smooth.differentiable (by simp) point)
    (second.smooth.differentiable (by simp) point)]
  rfl

/-- The true angular inverse has the exact compact-test right inverse law.
The mean term is present, and no regularity of a field is involved. -/
theorem startupTrueInverseTest_rotation (test : TestFunction openUnitDisk) :
    startupRotationTest (startupTrueInverseTest test) =
      startupSubTest (startupAngularCompactTest (fun _ : ℝ => 1) contDiff_const test) test := by
  unfold startupTrueInverseTest
  rw [startupRotationTest_sub, startupRotationTest_angular, startupRotationTest_angular]
  apply startupTest_ext
  intro point
  change startupAngularTest (fun angle : ℝ => angle) (startupRotationDerivative test.toFun) point -
      startupAngularTest (fun _ : ℝ => 1)
        (startupRotationDerivative (startupAngularTest (fun angle : ℝ => angle) test.toFun)) point =
    startupAngularTest (fun _ : ℝ => 1) test.toFun point - test.toFun point
  rw [startupPrimitiveTest_rotation test.toFun test.smooth point,
    startupMeanTest_rotation_zero (startupAngularTest (fun angle : ℝ => angle) test.toFun)
      (startupAngularTest_smooth (fun angle : ℝ => angle) contDiff_id test.toFun test.smooth) point,
    sub_zero]

/-- Actual rough-field recovery after angular inversion, as a compact-test identity. -/
theorem startupTrueInverse_weakRotation_recovery (original source : StartupL2 3)
    (equation : ∀ (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk),
      -startupTestPairing cell vector (startupRotationTest test) original =
        startupTestPairing cell vector test source)
    (meanZero : startupRealAngularKernel (fun _ : ℝ => 1) contDiff_const original = 0)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test (startupTrueAngularInverse 3 0 source) =
      startupTestPairing cell vector test original := by
  have inversePair := congrArg (fun mapping : StartupL2 3 →L[ℂ] ℂ => mapping source)
    (startupTestPairing_trueInverse cell vector test)
  change startupTestPairing cell vector test (startupTrueAngularInverse 3 0 source) =
    startupTestPairing cell vector (startupTrueInverseTest test) source at inversePair
  rw [inversePair, ← equation, startupTrueInverseTest_rotation,
    startupTestPairing_sub, sub_apply]
  have meanPair := congrArg (fun mapping : StartupL2 3 →L[ℂ] ℂ => mapping original)
    (startupTestPairing_angular (fun _ : ℝ => 1) contDiff_const cell vector test)
  change startupTestPairing cell vector test (startupRealAngularKernel (fun _ : ℝ => 1) contDiff_const original) =
    startupTestPairing cell vector (startupAngularCompactTest (fun _ : ℝ => 1) contDiff_const test) original at meanPair
  rw [meanZero, map_zero] at meanPair
  rw [← meanPair, zero_sub, neg_neg]

end Grad.CartesianStartup
