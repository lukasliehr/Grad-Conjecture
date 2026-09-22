import AKBG5CoordinateCompactPairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier
open Grad.RepresentedKernel.SpatialProduct Grad.PhysicalFamily

theorem startupRotationTest_add (first second : TestFunction openUnitDisk) :
    startupRotationTest (startupAddTest first second) =
      startupAddTest (startupRotationTest first) (startupRotationTest second) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ (first.toFun + second.toFun) point (planeQuarterTurn point) =
    fderiv ℝ first.toFun point (planeQuarterTurn point) + fderiv ℝ second.toFun point (planeQuarterTurn point)
  rw [fderiv_add (first.smooth.differentiable (by simp) point) (second.smooth.differentiable (by simp) point)]
  rfl

theorem startupCovariantCompactTest_divergence (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (source : Fin 2) (test : TestFunction openUnitDisk) :
    startupAddTest
      (startupDerivativeTest 0 (startupCovariantCompactTest weight smooth source 0 test))
      (startupDerivativeTest 1 (startupCovariantCompactTest weight smooth source 1 test)) =
        startupAngularCompactTest weight smooth (startupDerivativeTest source test) := by
  apply startupTest_ext
  intro point
  change directionDerivative 0 (startupAngularTest (fun angle => weight angle * startupAverageWeight source 0 angle) test.toFun) point +
    directionDerivative 1 (startupAngularTest (fun angle => weight angle * startupAverageWeight source 1 angle) test.toFun) point = _
  exact (Fin.sum_univ_two _).symm.trans
    (startupCovariantAngularTest_divergence weight smooth source test.toFun test.smooth point)

/-- The scalar term in the force equation becomes the SAME gradient after
applying C, with the scalar mean explicitly retained before its gauge is used. -/
theorem startupCovariantPrimitiveCompact_gradientRotation (source : Fin 2) (test : TestFunction openUnitDisk) :
    startupAddTest
      (startupRotationTest (startupDerivativeTest 0 (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source 0 test)))
      (startupRotationTest (startupDerivativeTest 1 (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source 1 test))) =
        startupSubTest (startupMeanTest (startupDerivativeTest source test)) (startupDerivativeTest source test) := by
  rw [← startupRotationTest_add, startupCovariantCompactTest_divergence, startupRotationTest_angular]
  apply startupTest_ext
  intro point
  exact startupPrimitiveTest_rotation (startupDerivativeTest source test).toFun (startupDerivativeTest source test).smooth point

/-- Bundled compact form of C(R-J)=I-A, ready for the actual weak force. -/
theorem startupCovariantPrimitiveCompact_rotation (source target : Fin 2) (test : TestFunction openUnitDisk) :
    startupRotationTest (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source target test) =
      startupSubTest
        (startupAddTest
          (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test)
          (startupAddTest
            (multiplyTest (fun _ : Spatial => startupQuarterEntry target 0) contDiff_const
              (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source 0 test))
            (multiplyTest (fun _ : Spatial => startupQuarterEntry target 1) contDiff_const
              (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source 1 test))))
        (multiplyTest (fun _ : Spatial => if source = target then (1 : ℝ) else 0) contDiff_const test) := by
  unfold startupCovariantCompactTest
  rw [startupRotationTest_angular]
  apply startupTest_ext
  intro point
  change startupCovariantAngularTest (fun angle : ℝ => angle) source target
    (startupRotationDerivative test.toFun) point =
      startupCovariantAngularTest (fun _ : ℝ => 1) source target test.toFun point +
        (startupQuarterEntry target 0 * startupCovariantAngularTest (fun angle : ℝ => angle) source 0 test.toFun point +
          startupQuarterEntry target 1 * startupCovariantAngularTest (fun angle : ℝ => angle) source 1 test.toFun point) -
        (if source = target then 1 else 0 : ℝ) * test.toFun point
  simpa only [Fin.sum_univ_two] using startupCovariantPrimitiveTest_rotation source target test.toFun test.smooth point

end Grad.CartesianStartup
