import AKBG11ScalarThirdElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.PhysicalFamily Grad.NonlinearQuotient

theorem startupDerivativeTest_commute (first second : Fin 2) (test : TestFunction openUnitDisk) :
    startupDerivativeTest first (startupDerivativeTest second test) =
      startupDerivativeTest second (startupDerivativeTest first test) := by
  apply startupTest_ext
  intro point
  exact directionDerivative_commute isOpen_univ first second test.smooth.contDiffOn (mem_univ point)

theorem startupRotationDerivative_commutator (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (direction : Fin 2) (point : Spatial) :
    directionDerivative direction (startupRotationDerivative test) point =
      startupRotationDerivative (directionDerivative direction test) point +
        fderiv ℝ test point (planeQuarterTurn (spatialDirection direction)) := by
  have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ test) := (contDiff_infty_iff_fderiv.mp smooth).2
  have derivative := derivativeSmooth.differentiable (by simp) point
  change fderiv ℝ (fun source => fderiv ℝ test source (quarterTurnCLM source)) point
      (spatialDirection direction) =
    fderiv ℝ (fun source => fderiv ℝ test source (spatialDirection direction)) point
      (planeQuarterTurn point) + fderiv ℝ test point (planeQuarterTurn (spatialDirection direction))
  rw [fderiv_clm_apply derivative quarterTurnCLM.differentiableAt,
    fderiv_clm_apply derivative (differentiableAt_const (spatialDirection direction))]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  have symmetric := ((smooth.contDiffAt (x := point)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eq
      (spatialDirection direction) (planeQuarterTurn point)
  change fderiv ℝ test point (planeQuarterTurn (spatialDirection direction)) +
    fderiv ℝ (fderiv ℝ test) point (spatialDirection direction) (planeQuarterTurn point) = _
  rw [symmetric]
  ring

theorem startupQuarter_direction_zero : planeQuarterTurn (spatialDirection 0) = spatialDirection 1 := by
  ext coordinate
  fin_cases coordinate <;> norm_num [planeQuarterTurn, spatialDirection]

theorem startupQuarter_direction_one : planeQuarterTurn (spatialDirection 1) = -spatialDirection 0 := by
  ext coordinate
  fin_cases coordinate <;> norm_num [planeQuarterTurn, spatialDirection]

theorem startupRotationDerivativeTest_zero (test : TestFunction openUnitDisk) :
    startupRotationTest (startupDerivativeTest 0 test) =
      startupSubTest (startupDerivativeTest 0 (startupRotationTest test)) (startupDerivativeTest 1 test) := by
  apply startupTest_ext
  intro point
  change startupRotationDerivative (directionDerivative 0 test.toFun) point =
    directionDerivative 0 (startupRotationDerivative test.toFun) point - directionDerivative 1 test.toFun point
  rw [startupRotationDerivative_commutator test.toFun test.smooth, startupQuarter_direction_zero]
  simp only [directionDerivative]
  ring

theorem startupRotationDerivativeTest_one (test : TestFunction openUnitDisk) :
    startupRotationTest (startupDerivativeTest 1 test) =
      startupAddTest (startupDerivativeTest 1 (startupRotationTest test)) (startupDerivativeTest 0 test) := by
  apply startupTest_ext
  intro point
  change startupRotationDerivative (directionDerivative 1 test.toFun) point =
    directionDerivative 1 (startupRotationDerivative test.toFun) point + directionDerivative 0 test.toFun point
  rw [startupRotationDerivative_commutator test.toFun test.smooth, startupQuarter_direction_one, map_neg]
  simp only [directionDerivative]
  ring

end Grad.CartesianStartup
