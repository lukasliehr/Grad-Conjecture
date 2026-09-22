import AKBN3ScaledDerivativeForcePairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation

/-- The original rough projected force scales to psi=Xi(ell Y)/ell and
unchanged covariant amplitude. The actual Qrad test is preserved. -/
theorem startupProjectedForceEquation_dilation (scale : Scale)
    (psi : StartupL2 1) (covariant right : StartupL2 2)
    (equation : StartupWeakProjectedForceEquation psi covariant right) :
    StartupWeakProjectedForceEquation ((scale.val : ℂ)⁻¹ • startupMomentDilation scale psi)
      (startupMomentDilation scale covariant) (startupMomentDilation scale right) := by
  intro cell source test
  rw [startupCoordinateTestPairing_dilation,equation,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro target _
  rw [startupCoordinateTestPairing_dilation_gradient,startupWeakForceVectorPairing_dilation,startupPulledTest_qrad]
  simp only [smul_add,smul_neg]

/-- The rotational third equation has the exact axial multiplier ell/L. -/
theorem startupThirdEquation_dilation (scale : Scale) (axial : ℤ → ℂ)
    (theta scalar source : StartupL2 1)
    (equation : StartupWeakThirdEquation axial theta scalar source) :
    StartupWeakThirdEquation (fun cell => (scale.val : ℂ) * axial cell)
      ((scale.val : ℂ)⁻¹ • startupMomentDilation scale theta)
      (startupMomentDilation scale scalar) (startupMomentDilation scale source) := by
  intro cell test
  rw [startupCoordinateTestPairing_dilation,equation,startupCoordinateTestPairing_dilation_rotation,
    map_smul,startupCoordinateTestPairing_dilation_rotation]
  have nonzero : (scale.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale.property.1.ne'
  simp only [Complex.real_smul,smul_eq_mul]
  field_simp

end Grad.CartesianStartup
