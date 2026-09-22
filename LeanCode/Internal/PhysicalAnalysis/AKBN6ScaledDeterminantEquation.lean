import AKBN3ScaledDerivativeForcePairings
import AKBN5ScaledProjectionKernels

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation

theorem startupCoordinateTestPairing_dilation_derivative {dimension : ℕ} (scale : Scale)
    (field : StartupL2 dimension) (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupCoordinateTestPairing cell coordinate (startupDerivativeTest direction test) (startupMomentDilation scale field) =
      (scale.val : ℂ) • ((scale.val ^ 2)⁻¹ • startupCoordinateTestPairing cell coordinate
        (startupDerivativeTest direction (startupPulledTest scale test)) field) := by
  have given := startupCoordinateTestPairing_dilation_gradient scale field cell coordinate test direction
  rw [map_smul] at given
  have nonzero : (scale.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale.property.1.ne'
  simpa only [smul_smul,mul_inv_cancel₀ nonzero,one_smul] using congrArg ((scale.val : ℂ) • ·) given

theorem startupWeakDivergencePairing_dilation (scale : Scale) (field : StartupL2 2)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (startupMomentDilation scale field) cell test =
      (scale.val : ℂ) • ((scale.val ^ 2)⁻¹ • startupWeakDivergencePairing field cell (startupPulledTest scale test)) := by
  unfold startupWeakDivergencePairing
  rw [startupCoordinateTestPairing_dilation_derivative,startupCoordinateTestPairing_dilation_derivative]
  simp only [smul_sub,smul_neg]

/-- The genuine determinant row preserves its outer P0 and obtains exactly
G=ell*g/L and the axial symbol i*n*ell/L under physical dilation. -/
theorem startupDeterminantEquation_dilation (scale : Scale) (axial : ℤ → ℂ)
    (vector planarFlux : StartupL2 2) (scalar determinant scalarFlux : StartupL2 1)
    (equation : StartupWeakDeterminantEquation axial vector scalar determinant planarFlux scalarFlux) :
    StartupWeakDeterminantEquation (fun cell => (scale.val : ℂ) * axial cell)
      (startupMomentDilation scale vector) (startupMomentDilation scale scalar)
      ((scale.val : ℂ) • startupMomentDilation scale determinant)
      (startupMomentDilation scale planarFlux) (startupMomentDilation scale scalarFlux) := by
  intro cell test
  rw [map_smul,startupCoordinateTestPairing_dilation,equation,
    startupWeakDivergencePairing_dilation,startupWeakDivergencePairing_dilation,
    startupCoordinateTestPairing_dilation,startupCoordinateTestPairing_dilation,startupPulledTest_meanFree]
  simp only [Complex.real_smul,smul_eq_mul]
  ring

end Grad.CartesianStartup
