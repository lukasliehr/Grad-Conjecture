import AKAX6LiteralRealTensorFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct

/-- Use the accepted complex-linear weak pairing on the SAME disk field. -/
def startupTestPairing (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    StartupL2 3 →L[ℂ] ℂ :=
  Grad.WeakTesting.compactPairing 3 openUnitDisk cell vector test.toFun test.smooth test.compact

theorem startupTestPairing_apply (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk)
    (field : StartupL2 3) :
    startupTestPairing cell vector test field =
      ∫ point in openUnitDisk, test.toFun point • inner ℂ vector (field point cell) :=
  Grad.WeakTesting.compactPairing_apply 3 openUnitDisk cell vector test.toFun test.smooth test.compact field

theorem startupTestDerivative_supported (test : Spatial → ℝ) (direction : Fin 2) :
    tsupport (directionDerivative direction test) ⊆ tsupport test :=
  (tsupport_comp_subset (g := fun derivative : Spatial →L[ℝ] ℝ => derivative (spatialDirection direction))
    rfl (fderiv ℝ test)).trans (tsupport_fderiv_subset ℝ)

def startupDerivativeTest (direction : Fin 2) (test : TestFunction openUnitDisk) : TestFunction openUnitDisk where
  toFun := directionDerivative direction test.toFun
  smooth := startupTestDerivative_smooth test.toFun test.smooth direction
  compact := startupTestDerivative_compact test.toFun test.compact direction
  supported := (startupTestDerivative_supported test.toFun direction).trans test.supported

/-- Operator equality of the literal angular transpose, with no representative choices. -/
theorem startupTestPairing_angular (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    (startupTestPairing cell vector test).comp (startupRealAngularKernel weight smooth) =
      startupTestPairing cell vector (startupAngularCompactTest weight smooth test) := by
  ext field
  simp only [ContinuousLinearMap.comp_apply, startupTestPairing_apply]
  exact startupRealAngularKernel_transpose weight smooth field cell vector test.toFun test.smooth test.compact

/-- Exact transpose covariance expressed in the existing weak-test operator space. -/
theorem startupTestPairing_angularDerivative (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest direction (startupAngularCompactTest weight smooth test)) =
      ∑ coordinate : Fin 2,
        (startupTestPairing cell vector (startupDerivativeTest coordinate test)).comp
          (startupRealAngularKernel (startupRealCovectorWeight weight direction coordinate)
            (startupRealCovectorWeight_smooth weight smooth direction coordinate)) := by
  ext field
  simp only [sum_apply, ContinuousLinearMap.comp_apply, startupTestPairing_apply]
  exact startupAngular_derivative_transpose weight smooth test.toFun test.smooth test.compact
    field cell vector direction

end Grad.CartesianStartup
