import AKCO20ActualOriginalAllPowerStartup

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.PhysicalFamily Grad.ActualCartesianWeakEquations
open Grad.ActualSmoothPhysicalField

/-- The genuine angular generator is the divergence of its two polynomial
flux tests. The diagonal coefficient derivatives vanish exactly. -/
theorem startupRotationTest_polynomialDivergence (test : TestFunction openUnitDisk) :
    startupRotationTest test = startupAddTest
      (startupDerivativeTest 0 (multiplyTest (angularRotationCoordinate 0) (angularRotationCoordinate 0).contDiff test))
      (startupDerivativeTest 1 (multiplyTest (angularRotationCoordinate 1) (angularRotationCoordinate 1).contDiff test)) := by
  apply startupTest_ext
  intro point
  have identity := angularTransportFlux_divergence test.toFun point
    (test.smooth.differentiable (by simp) point)
  change fderiv ℝ test.toFun point (planeQuarterTurn point) =
    Grad.RepresentedKernel.SpatialProduct.directionDerivative 0 (angularTransportFlux test.toFun 0) point +
      Grad.RepresentedKernel.SpatialProduct.directionDerivative 1 (angularTransportFlux test.toFun 1) point
  simpa only [Fin.sum_univ_two] using identity.symm

/-- Literal psi=RTheta is the polynomial `(Jy)·gradient`, established on
rough native fields by weak separation. This supplies the scalar recovery
without multiplying an arbitrary smooth S/r by the nonsmooth radius. -/
theorem startupSame_scalarRotation_pairing (theta psi : StartupL2 1) (gradient : StartupL2 2)
    (rotation : ∀ cell test, -startupCoordinateTestPairing cell 0 (startupRotationTest test) theta =
      startupCoordinateTestPairing cell 0 test psi)
    (derivatives : ∀ cell direction test,
      -startupCoordinateTestPairing cell 0 (startupDerivativeTest direction test) theta =
        startupCoordinateTestPairing cell direction test gradient)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 test psi =
      ∑ direction : Fin 2, startupCoordinateTestPairing cell direction
        (multiplyTest (angularRotationCoordinate direction) (angularRotationCoordinate direction).contDiff test) gradient := by
  rw [← rotation cell test,startupRotationTest_polynomialDivergence,startupCoordinateTestPairing_add,add_apply,neg_add]
  rw [derivatives,derivatives,Fin.sum_univ_two]

/-- The actual mean-free scalar and original force row determine the SAME
scalar polynomial from the already recovered covariant gradient. -/
theorem startupSame_scalarForce_polynomial (psi : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation (originalScalarInverseKernel psi) vector right)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 test psi =
      ∑ direction : Fin 2, startupCoordinateTestPairing cell direction
        (multiplyTest (angularRotationCoordinate direction) (angularRotationCoordinate direction).contDiff test)
          (startupRecoveredGradient vector right) :=
  startupSame_scalarRotation_pairing (originalScalarInverseKernel psi) psi (startupRecoveredGradient vector right)
    (startupSame_scalarPrimitive_rotation psi mean)
    (startupSame_weakGradient _ vector right equation (startupSame_scalarPrimitive_mean psi mean)) cell test

end Grad.CartesianStartup
