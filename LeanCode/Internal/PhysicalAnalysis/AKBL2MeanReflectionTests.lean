import AKBL1SameFixedScalarGauge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier

theorem startupMeanTest_rotation_invariant (test : TestFunction openUnitDisk) (angle : ℝ) (point : Spatial) :
    (startupMeanTest test).toFun (planeRotationEquiv angle point) = (startupMeanTest test).toFun point := by
  have derivative (parameter : ℝ) : HasDerivAt
      (fun value : ℝ => startupAngularTest (fun _ : ℝ => 1) test.toFun (planeRotationEquiv (-value) point)) 0 parameter := by
    have actual := startupInverseOrbit_hasDerivAt (startupAngularTest (fun _ : ℝ => 1) test.toFun)
      (startupAngularTest_smooth _ contDiff_const test.toFun test.smooth) point parameter
    simpa only [startupAngularTest_rotation (fun _ : ℝ => 1) contDiff_const test.toFun test.smooth,
      startupMeanTest_rotation_zero test.toFun test.smooth, neg_zero] using actual
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := -angle) (fun parameter _ => derivative parameter)
    (continuous_const.intervalIntegrable 0 (-angle))
  rw [intervalIntegral.integral_zero, neg_neg, startupInverseRotation_zero] at fundamental
  exact sub_eq_zero.mp fundamental.symm

theorem startupPoint_polar_rotation (point : Spatial) :
    ∃ angle : ℝ, planeRotationEquiv angle (‖point‖ • spatialDirection 0) = point := by
  refine ⟨Complex.arg (signedComplexCoordinate 1 point), ?_⟩
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change Real.cos (Complex.arg (signedComplexCoordinate 1 point)) * (‖point‖ * 1) -
      Real.sin (Complex.arg (signedComplexCoordinate 1 point)) * (‖point‖ * 0) = point 0
    rw [mul_one, mul_zero, mul_zero, sub_zero, mul_comm, ← signedComplexCoordinate_one_norm, Complex.norm_mul_cos_arg]
    simp [signedComplexCoordinate]
  · change Real.sin (Complex.arg (signedComplexCoordinate 1 point)) * (‖point‖ * 1) +
      Real.cos (Complex.arg (signedComplexCoordinate 1 point)) * (‖point‖ * 0) = point 1
    rw [mul_one, mul_zero, mul_zero, add_zero, mul_comm, ← signedComplexCoordinate_one_norm, Complex.norm_mul_sin_arg]
    simp [signedComplexCoordinate]

theorem startupReflection_rotated_axis (angle radius : ℝ) :
    cartesianReflectionEquiv (planeRotationEquiv angle (radius • spatialDirection 0)) =
      planeRotationEquiv (-angle) (radius • spatialDirection 0) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [cartesianReflectionEquiv, cartesianReflection, planeRotation, spatialDirection]

/-- The actual scalar mean test is reflection invariant, derived from its
vanishing R derivative and the full Cartesian polar coverage. -/
theorem startupReflection_meanTest (test : TestFunction openUnitDisk) :
    startupReflectionTest (startupMeanTest test) = startupMeanTest test := by
  apply startupTest_ext
  intro point
  obtain ⟨angle, polar⟩ := startupPoint_polar_rotation point
  change (startupMeanTest test).toFun (cartesianReflectionEquiv point) = (startupMeanTest test).toFun point
  rw [← polar, startupReflection_rotated_axis, startupMeanTest_rotation_invariant,
    startupMeanTest_rotation_invariant]

theorem startupReflection_direction (direction : Fin 2) :
    cartesianReflectionEquiv (spatialDirection direction) =
      (if direction = 0 then 1 else -1 : ℝ) • spatialDirection direction := by
  apply PiLp.ext
  intro coordinate
  fin_cases direction <;> fin_cases coordinate <;>
    simp [cartesianReflectionEquiv, cartesianReflection, spatialDirection]

theorem startupDerivativeTest_reflection (direction : Fin 2) (test : TestFunction openUnitDisk) :
    startupDerivativeTest direction (startupReflectionTest test) =
      multiplyTest (fun _ : Spatial => if direction = 0 then (1 : ℝ) else -1) contDiff_const
        (startupReflectionTest (startupDerivativeTest direction test)) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ (test.toFun ∘ cartesianReflectionEquiv) point (spatialDirection direction) =
    (if direction = 0 then 1 else -1 : ℝ) *
      fderiv ℝ test.toFun (cartesianReflectionEquiv point) (spatialDirection direction)
  rw [fderiv_comp point (test.smooth.differentiable (by simp) (cartesianReflectionEquiv point))
    cartesianReflectionEquiv.toContinuousLinearEquiv.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.fderiv]
  change fderiv ℝ test.toFun (cartesianReflectionEquiv point)
    (cartesianReflectionEquiv (spatialDirection direction)) = _
  rw [startupReflection_direction, map_smul]
  rfl

end Grad.CartesianStartup
