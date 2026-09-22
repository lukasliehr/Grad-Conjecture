import AKAX7CompactPairingOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel.SpatialProduct

theorem startupTest_ext {first second : TestFunction openUnitDisk}
    (same : ∀ point, first.toFun point = second.toFun point) : first = second := by
  cases first with
  | mk first firstSmooth firstCompact firstSupported =>
    cases second with
    | mk second secondSmooth secondCompact secondSupported =>
      have equality : first = second := funext same
      cases equality
      rfl

def startupSubTest (first second : TestFunction openUnitDisk) : TestFunction openUnitDisk where
  toFun := first.toFun - second.toFun
  smooth := first.smooth.sub second.smooth
  compact := first.compact.sub second.compact
  supported := (tsupport_sub first.toFun second.toFun).trans (union_subset first.supported second.supported)

theorem startupTestPairing_sub (cell : ℤ) (vector : PhysicalValue 3)
    (first second : TestFunction openUnitDisk) :
    startupTestPairing cell vector (startupSubTest first second) =
      startupTestPairing cell vector first - startupTestPairing cell vector second := by
  ext field
  simp only [sub_apply, startupTestPairing_apply]
  change (∫ point in openUnitDisk, (first.toFun point - second.toFun point) • inner ℂ vector (field point cell)) = _
  simp_rw [sub_smul]
  exact integral_sub
    (Grad.WeakTesting.pairing_integrable 3 openUnitDisk cell vector first.toFun
      (first.smooth.continuous.memLp_of_hasCompactSupport first.compact) field)
    (Grad.WeakTesting.pairing_integrable 3 openUnitDisk cell vector second.toFun
      (second.smooth.continuous.memLp_of_hasCompactSupport second.compact) field)

theorem startupDerivativeTest_sub (direction : Fin 2) (first second : TestFunction openUnitDisk) :
    startupDerivativeTest direction (startupSubTest first second) =
      startupSubTest (startupDerivativeTest direction first) (startupDerivativeTest direction second) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ (first.toFun - second.toFun) point (spatialDirection direction) =
    fderiv ℝ first.toFun point (spatialDirection direction) - fderiv ℝ second.toFun point (spatialDirection direction)
  rw [fderiv_sub (first.smooth.differentiable (by simp) point) (second.smooth.differentiable (by simp) point)]
  rfl

/-- The transpose reverses composition: remove the mean AFTER the primitive on the test. -/
def startupTrueInverseTest (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  startupSubTest (startupAngularCompactTest (fun angle : ℝ => angle) contDiff_id test)
    (startupAngularCompactTest (fun _ : ℝ => 1) contDiff_const
      (startupAngularCompactTest (fun angle : ℝ => angle) contDiff_id test))

theorem startupTestPairing_trueInverse (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) :
    (startupTestPairing cell vector test).comp (startupTrueAngularInverse 3 0) =
      startupTestPairing cell vector (startupTrueInverseTest test) := by
  rw [startupTrueAngularInverse, neg_zero, startupZeroPrimitive_real, startupZeroMean_real]
  rw [← ContinuousLinearMap.comp_assoc, startupTestPairing_angular]
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, startupTestPairing_angular]
  exact (startupTestPairing_sub cell vector _ _).symm

end Grad.CartesianStartup
