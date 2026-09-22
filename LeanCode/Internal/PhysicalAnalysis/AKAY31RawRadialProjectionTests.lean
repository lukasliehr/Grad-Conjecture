import AKAY22ProjectedRawForceTests
import AKAB8PuncturedCutoffTest

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.WeightedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.WeightedAxisRemoval

/-- Unbundled actual transpose used by the original punctured-force axis removal. -/
def startupRawQradTest (source : Fin 2) (test : Spatial → ℝ) (target : Fin 2) (point : Spatial) : ℝ :=
  (if target = source then 1 else 0) * test point - (1 / 2 : ℝ) *
    (startupAngularTest (fun angle => startupInverseRotationEntry source target (-angle)) test point +
      (if source = 0 then 1 else -1) *
        startupAngularTest (fun angle => startupInverseRotationEntry source target (-angle))
          (fun query => test (cartesianReflectionEquiv query)) point)

theorem startupRawQradTest_same (source target : Fin 2) (test : TestFunction openUnitDisk) :
    startupRawQradTest source test.toFun target = (startupQradTestComponent target source test).toFun := rfl

theorem startupRawQradTest_smooth (source : Fin 2) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (target : Fin 2) :
    ContDiff ℝ ∞ (startupRawQradTest source test target) := by
  exact (contDiff_const.mul smooth).sub (contDiff_const.mul
    ((startupAngularTest_smooth _ ((startupInverseRotationEntry_smooth source target).comp contDiff_id.neg) test smooth).add
      (contDiff_const.mul (startupAngularTest_smooth _
        ((startupInverseRotationEntry_smooth source target).comp contDiff_id.neg) _
        (smooth.comp cartesianReflectionEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff)))))

theorem startupRawQradTest_compact (source : Fin 2) (test : Spatial → ℝ)
    (compact : HasCompactSupport test) (target : Fin 2) :
    HasCompactSupport (startupRawQradTest source test target) := by
  exact compact.mul_left.sub ((startupAngularTest_compact _ test compact).add
    ((startupAngularTest_compact _ _ (compact.comp_homeomorph cartesianReflectionEquiv.toHomeomorph)).mul_left)).mul_left

theorem startupAngularTest_radial_product (weight : ℝ → ℝ) (scalar test : Spatial → ℝ)
    (radial : ∀ angle point, scalar (planeRotationEquiv angle point) = scalar point) :
    startupAngularTest weight (fun point => scalar point * test point) =
      fun point => scalar point * startupAngularTest weight test point := by
  funext point
  unfold startupAngularTest
  have integrands : (fun angle => weight angle * (scalar (planeRotationEquiv (-angle) point) *
      test (planeRotationEquiv (-angle) point))) =
      fun angle => scalar point * (weight angle * test (planeRotationEquiv (-angle) point)) := by
    funext angle
    rw [radial (-angle) point]
    ring
  rw [integrands, integral_const_mul]
  ring

theorem startupRawQradTest_radial_product (scalar test : Spatial → ℝ)
    (radial : ∀ angle point, scalar (planeRotationEquiv angle point) = scalar point)
    (reflected : ∀ point, scalar (cartesianReflectionEquiv point) = scalar point)
    (source target : Fin 2) :
    startupRawQradTest source (fun point => scalar point * test point) target =
      fun point => scalar point * startupRawQradTest source test target point := by
  have reflection : (fun query => scalar (cartesianReflectionEquiv query) * test (cartesianReflectionEquiv query)) =
      fun query => scalar query * test (cartesianReflectionEquiv query) := by
    funext query
    rw [reflected query]
  unfold startupRawQradTest
  rw [reflection, startupAngularTest_radial_product _ scalar test radial,
    startupAngularTest_radial_product _ scalar (fun query => test (cartesianReflectionEquiv query)) radial]
  funext point
  ring

/-- Literal radial axis cutoff commutation required by AKBE2. -/
theorem startupRawQradTest_axisCutoff (source : Fin 2) (epsilon : ℝ)
    (test : Spatial → ℝ) (target : Fin 2) :
    startupRawQradTest source (axisCutoffTest epsilon test) target =
      axisCutoffTest epsilon (startupRawQradTest source test target) := by
  exact startupRawQradTest_radial_product (axisCutoff epsilon) test
    (fun angle point => axisCutoff_same_norm epsilon _ _ (LinearIsometryEquiv.norm_map _ _))
    (fun point => axisCutoff_same_norm epsilon _ _ (LinearIsometryEquiv.norm_map _ _)) source target

end Grad.CartesianStartup
