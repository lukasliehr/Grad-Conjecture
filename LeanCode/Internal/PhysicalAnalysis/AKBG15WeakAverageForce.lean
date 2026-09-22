import AKBG14WeakPlanarLaplacian

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier
open Grad.RepresentedKernel.SpatialProduct

 theorem startupCovariantAverageCompact_rotation (source target : Fin 2) (test : TestFunction openUnitDisk) :
    startupRotationTest (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test) =
      startupAddTest
        (multiplyTest (fun _ : Spatial => startupQuarterEntry target 0) contDiff_const
          (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source 0 test))
        (multiplyTest (fun _ : Spatial => startupQuarterEntry target 1) contDiff_const
          (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source 1 test)) := by
  unfold startupCovariantCompactTest
  rw [startupRotationTest_angular]
  apply startupTest_ext
  intro point
  exact (startupCovariantAverageTest_rotation source target test.toFun test.smooth point).trans (Fin.sum_univ_two _)

 theorem startupAverage_theta_term (theta : StartupL2 1) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    (∑ target : Fin 2, startupCoordinateTestPairing cell 0
      (startupRotationTest (startupDerivativeTest target
        (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test))) theta) = 0 := by
  rw [Fin.sum_univ_two, ← add_apply, ← startupCoordinateTestPairing_add,
    ← startupRotationTest_add, startupCovariantCompactTest_divergence, startupRotationTest_angular,
    startupCoordinateTestPairing_apply]
  change (∫ point in openUnitDisk, startupAngularTest (fun _ : ℝ => 1)
    (startupRotationDerivative (startupDerivativeTest source test).toFun) point • theta point cell 0) = 0
  simp only [startupMeanTest_rotation_zero (startupDerivativeTest source test).toFun
    (startupDerivativeTest source test).smooth, zero_smul, MeasureTheory.integral_zero]

 theorem startupAverage_vector_term (vector : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    (∑ target : Fin 2,
      (startupCoordinateTestPairing cell target
        (startupRotationTest (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test)) vector -
        startupCoordinateTestPairing cell target
          (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test)
            (originalValueKernel quarterValueMap vector))) =
      -(2 : ℂ) * startupCoordinateTestPairing cell source test
        (originalAverageKernel (originalValueKernel quarterValueMap vector)) := by
  rw [startupAverage_pairing]
  simp_rw [startupCovariantAverageCompact_rotation, startupCoordinateTestPairing_add,
    startupCoordinateTestPairing_real_smul, add_apply, smul_apply, startupCoordinateTestPairing_quarter]
  fin_cases source <;> simp only [Fin.sum_univ_two, startupQuarterEntry] <;> norm_num <;> ring

/-- The equivariant mean is determined by the genuine force. It is not
set to zero; it supplies the actual J A(force-correction)/2 term in ER11. -/
theorem startupSame_force_average (theta : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation theta vector right) :
    originalAverageKernel right = -(2 : ℂ) •
      originalValueKernel quarterValueMap (originalAverageKernel vector) := by
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  rw [map_smul, startupAverage_pairing]
  have rows (target : Fin 2) := equation cell target
    (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const coordinate target test)
  simp_rw [rows]
  have regroup (scalar first second : Fin 2 → ℂ) :
      (∑ target, (scalar target + first target - second target)) =
        (∑ target, scalar target) + (∑ target, (first target - second target)) := by
    simp only [Fin.sum_univ_two]
    ring
  rw [regroup, startupAverage_theta_term, startupAverage_vector_term, startupAverage_quarter, zero_add]
  rfl

end Grad.CartesianStartup
