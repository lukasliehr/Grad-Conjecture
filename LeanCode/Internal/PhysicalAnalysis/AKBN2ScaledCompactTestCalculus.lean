import AKBN1ScaledCompactPairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation
open Grad.Constraints Grad.WeightedJets.SpatialMultiplier Grad.RepresentedKernel.SpatialProduct
open Grad.PhysicalFamily Grad.NonlinearQuotient Grad.GaugeCoefficients.Radial

theorem startupPulledTest_add (scale : Scale) (first second : TestFunction openUnitDisk) :
    startupPulledTest scale (startupAddTest first second) =
      startupAddTest (startupPulledTest scale first) (startupPulledTest scale second) := by
  apply startupTest_ext
  intro point
  rfl

theorem startupPulledTest_sub (scale : Scale) (first second : TestFunction openUnitDisk) :
    startupPulledTest scale (startupSubTest first second) =
      startupSubTest (startupPulledTest scale first) (startupPulledTest scale second) := by
  apply startupTest_ext
  intro point
  rfl

theorem startupPulledTest_const_mul (scale : Scale) (scalar : ℝ) (test : TestFunction openUnitDisk) :
    startupPulledTest scale (multiplyTest (fun _ : Spatial => scalar) contDiff_const test) =
      multiplyTest (fun _ : Spatial => scalar) contDiff_const (startupPulledTest scale test) := by
  apply startupTest_ext
  intro point
  rfl

/-- Spatial derivatives of the existing compact pullback have the exact inverse scale. -/
theorem startupPulledTest_derivative (scale : Scale) (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupDerivativeTest direction (startupPulledTest scale test) =
      multiplyTest (fun _ : Spatial => scale.val⁻¹) contDiff_const
        (startupPulledTest scale (startupDerivativeTest direction test)) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ (fun current : Spatial => test.toFun (scale.val⁻¹ • current)) point (spatialDirection direction) =
    scale.val⁻¹ * fderiv ℝ test.toFun (scale.val⁻¹ • point) (spatialDirection direction)
  have scaled := congrFun (orderedDerivative_scale scale.val⁻¹ 1 (fun _ : Fin 1 => direction) test.toFun test.smooth) point
  simpa only [Grad.WeakTesting.orderedTestDerivative,iteratedFDeriv_one_apply,pow_one] using scaled

/-- The angular derivative is invariant under the original positive dilation. -/
theorem startupPulledTest_rotation (scale : Scale) (test : TestFunction openUnitDisk) :
    startupRotationTest (startupPulledTest scale test) = startupPulledTest scale (startupRotationTest test) := by
  apply startupTest_ext
  intro point
  have derivative : HasFDerivAt (fun current : Spatial => test.toFun (scale.val⁻¹ • current))
      ((fderiv ℝ test.toFun (scale.val⁻¹ • point)).comp (scale.val⁻¹ • ContinuousLinearMap.id ℝ Spatial)) point :=
    (test.smooth.differentiable (by simp) _).hasFDerivAt.comp point
      ((hasFDerivAt_id point).const_smul scale.val⁻¹)
  change fderiv ℝ (fun current : Spatial => test.toFun (scale.val⁻¹ • current)) point (planeQuarterTurn point) =
    fderiv ℝ test.toFun (scale.val⁻¹ • point) (planeQuarterTurn (scale.val⁻¹ • point))
  rw [derivative.fderiv]
  change fderiv ℝ test.toFun (scale.val⁻¹ • point) (scale.val⁻¹ • planeQuarterTurn point) = _
  exact congrArg (fderiv ℝ test.toFun (scale.val⁻¹ • point)) ((quarterTurnCLM.map_smul scale.val⁻¹ point).symm)

/-- Dilation commutes with the actual full angular compact test integral. -/
theorem startupPulledTest_angular (scale : Scale) (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : TestFunction openUnitDisk) :
    startupPulledTest scale (startupAngularCompactTest weight weightSmooth test) =
      startupAngularCompactTest weight weightSmooth (startupPulledTest scale test) := by
  apply startupTest_ext
  intro point
  change startupAngularTest weight test.toFun (scale.val⁻¹ • point) =
    startupAngularTest weight (fun current => test.toFun (scale.val⁻¹ • current)) point
  unfold startupAngularTest
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro angle
  exact congrArg (fun current => weight angle * test.toFun current) ((planeRotationEquiv (-angle)).map_smul scale.val⁻¹ point)

theorem startupPulledTest_reflection (scale : Scale) (test : TestFunction openUnitDisk) :
    startupPulledTest scale (startupReflectionTest test) = startupReflectionTest (startupPulledTest scale test) := by
  apply startupTest_ext
  intro point
  change test.toFun (cartesianReflectionEquiv (scale.val⁻¹ • point)) =
    test.toFun (scale.val⁻¹ • cartesianReflectionEquiv point)
  rw [LinearIsometryEquiv.map_smul]

/-- The corrected original Qrad compact transpose commutes with dilation. -/
theorem startupPulledTest_qrad (scale : Scale) (source target : Fin 2) (test : TestFunction openUnitDisk) :
    startupPulledTest scale (startupQradTestComponent target source test) =
      startupQradTestComponent target source (startupPulledTest scale test) := by
  unfold startupQradTestComponent startupAverageTestComponent
  rw [startupPulledTest_sub,startupPulledTest_const_mul,startupPulledTest_const_mul,startupPulledTest_add,
    startupPulledTest_angular,startupPulledTest_const_mul,startupPulledTest_angular,startupPulledTest_reflection]

end Grad.CartesianStartup
