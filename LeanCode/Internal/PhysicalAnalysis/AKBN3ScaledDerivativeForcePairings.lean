import AKBN2ScaledCompactTestCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation
open Grad.Constraints Grad.Constraints.Gauges Grad.WeightedJets.SpatialMultiplier
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupCoordinateTestPairing_dilation_rotation {dimension : ℕ} (scale : Scale)
    (field : StartupL2 dimension) (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (startupRotationTest test) (startupMomentDilation scale field) =
      (scale.val ^ 2)⁻¹ • startupCoordinateTestPairing cell coordinate (startupRotationTest (startupPulledTest scale test)) field := by
  rw [startupCoordinateTestPairing_dilation,startupPulledTest_rotation]

/-- Dividing the scalar by ell precisely cancels the spatial derivative scale. -/
theorem startupCoordinateTestPairing_dilation_gradient {dimension : ℕ} (scale : Scale)
    (field : StartupL2 dimension) (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupCoordinateTestPairing cell coordinate (startupDerivativeTest direction test)
      ((scale.val : ℂ)⁻¹ • startupMomentDilation scale field) =
      (scale.val ^ 2)⁻¹ • startupCoordinateTestPairing cell coordinate
        (startupDerivativeTest direction (startupPulledTest scale test)) field := by
  rw [map_smul,startupCoordinateTestPairing_dilation,startupPulledTest_derivative,
    startupCoordinateTestPairing_real_smul]
  simp only [smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_inv]
  ring

/-- The literal -R-J force vector is invariant under the physical dilation. -/
theorem startupWeakForceVectorPairing_dilation (scale : Scale) (field : StartupL2 2)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupWeakForceVectorPairing (startupMomentDilation scale field) cell coordinate test =
      (scale.val ^ 2)⁻¹ • startupWeakForceVectorPairing field cell coordinate (startupPulledTest scale test) := by
  unfold startupWeakForceVectorPairing
  rw [startupCoordinateTestPairing_dilation_rotation,startupCoordinateTestPairing_quarter,
    startupCoordinateTestPairing_quarter]
  by_cases zero : coordinate = 0
  · rw [if_pos zero,if_pos zero,startupCoordinateTestPairing_dilation]
    simp only [smul_sub,smul_neg]
  · rw [if_neg zero,if_neg zero,startupCoordinateTestPairing_dilation]
    simp only [smul_sub]

end Grad.CartesianStartup
