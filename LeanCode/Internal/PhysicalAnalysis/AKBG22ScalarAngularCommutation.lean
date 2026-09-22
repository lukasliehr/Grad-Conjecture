import AKBG21ProjectedWeakForceConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

theorem startupInverseRotations_commute (first second : ℝ) (point : Spatial) :
    planeRotationEquiv (-second) (planeRotationEquiv (-first) point) =
      planeRotationEquiv (-first) (planeRotationEquiv (-second) point) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotation] <;> ring

theorem startupAngularTest_iterated (first second : ℝ → ℝ) (test : Spatial → ℝ) (point : Spatial) :
    startupAngularTest first (startupAngularTest second test) point =
      (2*Real.pi)⁻¹ * (2*Real.pi)⁻¹ *
        ∫ firstAngle in Icc (0 : ℝ) (2*Real.pi), ∫ secondAngle in Icc (0 : ℝ) (2*Real.pi),
          first firstAngle * second secondAngle *
            test (planeRotationEquiv (-secondAngle) (planeRotationEquiv (-firstAngle) point)) := by
  unfold startupAngularTest
  have inner (firstAngle : ℝ) : first firstAngle *
      ((2*Real.pi)⁻¹ * ∫ secondAngle in Icc (0 : ℝ) (2*Real.pi),
        second secondAngle * test (planeRotationEquiv (-secondAngle) (planeRotationEquiv (-firstAngle) point))) =
      (2*Real.pi)⁻¹ * ∫ secondAngle in Icc (0 : ℝ) (2*Real.pi),
        first firstAngle * second secondAngle * test (planeRotationEquiv (-secondAngle) (planeRotationEquiv (-firstAngle) point)) := by
    simp_rw [mul_assoc (first firstAngle) (second _) (test _)]
    rw [integral_const_mul]
    ring
  simp_rw [inner]
  rw [integral_const_mul]
  ring

/-- Scalar angular kernels commute because the actual spatial rotations
commute; Fubini is paid on the compact two-angle domain. -/
theorem startupAngularTest_commute (first second : ℝ → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupAngularTest first (startupAngularTest second test) point =
      startupAngularTest second (startupAngularTest first test) point := by
  have innerSmooth : ContDiff ℝ ∞ (fun angles : ℝ × ℝ => planeRotationEquiv (-angles.1) point) := by
    have insertion : ContDiff ℝ ∞ (fun angles : ℝ × ℝ => (point, angles.1)) :=
      contDiff_const.prodMk contDiff_fst
    simpa only [Function.comp_def] using startupInverseTestRotation_smooth.comp insertion
  have orbitSmooth : ContDiff ℝ ∞ (fun angles : ℝ × ℝ =>
      planeRotationEquiv (-angles.2) (planeRotationEquiv (-angles.1) point)) := by
    have insertion : ContDiff ℝ ∞ (fun angles : ℝ × ℝ =>
        (planeRotationEquiv (-angles.1) point, angles.2)) := innerSmooth.prodMk contDiff_snd
    simpa only [Function.comp_def] using startupInverseTestRotation_smooth.comp insertion
  have continuousIntegrand : Continuous (fun angles : ℝ × ℝ =>
      first angles.1 * second angles.2 *
        test (planeRotationEquiv (-angles.2) (planeRotationEquiv (-angles.1) point))) :=
    ((firstSmooth.comp contDiff_fst).mul (secondSmooth.comp contDiff_snd)).continuous.mul
      (testSmooth.comp orbitSmooth).continuous
  have integrable : Integrable (fun angles : ℝ × ℝ =>
      first angles.1 * second angles.2 *
        test (planeRotationEquiv (-angles.2) (planeRotationEquiv (-angles.1) point)))
      ((volume.restrict (Icc (0 : ℝ) (2*Real.pi))).prod (volume.restrict (Icc (0 : ℝ) (2*Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact continuousIntegrand.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [startupAngularTest_iterated, startupAngularTest_iterated, integral_integral_swap integrable]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with secondAngle
  apply integral_congr_ae
  filter_upwards [] with firstAngle
  rw [startupInverseRotations_commute firstAngle secondAngle]
  ring

theorem startupAngularCompactTest_commute (first second : ℝ → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (test : TestFunction openUnitDisk) :
    startupAngularCompactTest first firstSmooth (startupAngularCompactTest second secondSmooth test) =
      startupAngularCompactTest second secondSmooth (startupAngularCompactTest first firstSmooth test) := by
  apply startupTest_ext
  intro point
  exact startupAngularTest_commute first second firstSmooth secondSmooth test.toFun test.smooth point

end Grad.CartesianStartup
