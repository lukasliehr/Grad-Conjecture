import AKAY4CompactRotationGenerator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.Constraints Grad.PhysicalFamily
open Grad.GaugeCoefficients.Radial

theorem startupRotatedTest_rotation (angle : ℝ) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (scalar : ℝ) (point : Spatial) :
    startupRotationDerivative (fun source => scalar * test (planeRotationEquiv angle source)) point =
      scalar * startupRotationDerivative test (planeRotationEquiv angle point) := by
  have derivative := ((smooth.differentiable (by simp) (planeRotationEquiv angle point)).hasFDerivAt.comp point
    (planeRotationEquiv angle).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).const_mul scalar
  simp only [Function.comp_def] at derivative
  unfold startupRotationDerivative
  rw [derivative.fderiv]
  change scalar * fderiv ℝ test (planeRotationEquiv angle point)
    (planeRotationEquiv angle (planeQuarterTurn point)) = _
  rw [startupRotation_quarter]

/-- The actual angular integral commutes with the genuine rotation generator. -/
theorem startupAngularTest_rotation (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupRotationDerivative (startupAngularTest weight test) point =
      startupAngularTest weight (startupRotationDerivative test) point := by
  let integrand : Spatial × ℝ → ℝ := fun argument =>
    weight argument.2 * test (planeRotationEquiv (-argument.2) argument.1)
  have smooth : ContDiff ℝ ∞ integrand :=
    (weightSmooth.comp contDiff_snd).mul (testSmooth.comp startupInverseTestRotation_smooth)
  have derivative := (hasFDerivAt_compactIntegral isOpen_univ smooth.contDiffOn 0 (2 * Real.pi)
    point (mem_univ point)).const_mul ((2 * Real.pi)⁻¹ : ℝ)
  change fderiv ℝ (fun source => (2 * Real.pi)⁻¹ * ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    integrand (source, angle)) point (planeQuarterTurn point) = _
  rw [derivative.fderiv]
  change (2 * Real.pi)⁻¹ * (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    integralParameterDerivative integrand (point, angle)) (planeQuarterTurn point) = _
  have derivativeContinuous : Continuous (fun angle => integralParameterDerivative integrand (point, angle)) :=
    (integralParameterDerivative_smooth (domain := (univ : Set Spatial)) isOpen_univ smooth.contDiffOn).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨mem_univ _, mem_univ _⟩)
  rw [ContinuousLinearMap.integral_apply derivativeContinuous.integrableOn_Icc]
  unfold startupAngularTest
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [integralParameterDerivative_eq point angle (smooth.differentiable (by simp) (point, angle))]
  exact startupRotatedTest_rotation (-angle) test testSmooth (weight angle) point

theorem startupRotationTest_angular (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (test : TestFunction openUnitDisk) :
    startupRotationTest (startupAngularCompactTest weight smooth test) =
      startupAngularCompactTest weight smooth (startupRotationTest test) := by
  apply startupTest_ext
  intro point
  exact startupAngularTest_rotation weight smooth test.toFun test.smooth point

end Grad.CartesianStartup
