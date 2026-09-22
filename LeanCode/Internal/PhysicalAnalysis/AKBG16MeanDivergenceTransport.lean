import AKBG15WeakAverageForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier
open Grad.RepresentedKernel.SpatialProduct

theorem startupAverageWeight_covector (source target : Fin 2) :
    startupAverageWeight source target = fun angle => startupInverseRotationEntry target source angle := by
  funext angle
  fin_cases source <;> fin_cases target <;>
    simp [startupAverageWeight, startupInverseRotationEntry, planeRotation, spatialDirection]

theorem startupMeanTest_derivative (direction : Fin 2) (test : TestFunction openUnitDisk) :
    startupDerivativeTest direction (startupMeanTest test) =
      startupAddTest
        (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const 0 direction (startupDerivativeTest 0 test))
        (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const 1 direction (startupDerivativeTest 1 test)) := by
  apply startupTest_ext
  intro point
  change directionDerivative direction (startupAngularTest (fun _ : ℝ => 1) test.toFun) point = _
  rw [startupAngularTest_derivative (fun _ : ℝ => 1) contDiff_const test.toFun test.smooth,
    Fin.sum_univ_two]
  change startupAngularTest (fun angle => 1 * startupInverseRotationEntry direction 0 angle)
      (directionDerivative 0 test.toFun) point +
    startupAngularTest (fun angle => 1 * startupInverseRotationEntry direction 1 angle)
      (directionDerivative 1 test.toFun) point =
    startupAngularTest (fun angle => 1 * startupAverageWeight 0 direction angle)
      (directionDerivative 0 test.toFun) point +
    startupAngularTest (fun angle => 1 * startupAverageWeight 1 direction angle)
      (directionDerivative 1 test.toFun) point
  rw [startupAverageWeight_covector, startupAverageWeight_covector]

/-- Scalar angular mean of divergence is divergence of the actual equivariant
vector average, on arbitrary rough L2 fields and genuine compact tests. -/
theorem startupWeakDivergence_mean (vector : StartupL2 2) (cell : ℤ)
    (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing vector cell (startupMeanTest test) =
      startupWeakDivergencePairing (originalAverageKernel vector) cell test := by
  unfold startupWeakDivergencePairing
  rw [startupMeanTest_derivative, startupMeanTest_derivative,
    startupCoordinateTestPairing_add, startupCoordinateTestPairing_add, add_apply, add_apply,
    startupAverage_pairing, startupAverage_pairing, Fin.sum_univ_two, Fin.sum_univ_two]
  ring

theorem startupQuarter_twice (field : StartupL2 2) :
    originalValueKernel quarterValueMap (originalValueKernel quarterValueMap field) = -field :=
  congrArg (fun operator : StartupL2 2 →L[ℂ] StartupL2 2 => operator field) startupQuarter_square

theorem startupSame_force_average_recovery (theta : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation theta vector right) :
    originalAverageKernel vector =
      (1 / 2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel right) := by
  rw [startupSame_force_average theta vector right equation, map_smul, startupQuarter_twice]
  simp only [smul_neg, smul_smul]
  norm_num

end Grad.CartesianStartup
