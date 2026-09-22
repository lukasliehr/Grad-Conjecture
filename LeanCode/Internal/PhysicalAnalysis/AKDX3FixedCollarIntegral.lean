import AKDX2FixedReverseCollarBounds
import ARC6HalfCollarIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift
open Grad.DiskExtension.Operator

def fixedCollarIntegral (lower : ℝ) (function : ℝ × ℝ → ℝ) : ℝ :=
  ∫ angle in Ioo (-Real.pi) Real.pi, ∫ time in (0 : ℝ)..(1-lower), function (time,angle)

theorem disk_integral_le_fixedCollar (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (function : SpatialPlane → ℝ) (continuousFunction : Continuous function)
    (nonnegative : ∀ point, 0 ≤ function point)
    (vanishes : ∀ point, ‖point‖ ≤ lower → function point = 0) :
    (∫ point in closedUnitDisk, function point) ≤
      fixedCollarIntegral lower (fun point => function (collarPlane point)) := by
  let polarIntegrand : ℝ × ℝ → ℝ := fun point =>
    point.1 * function (spatialPlaneOfPair (polarCoord.symm point))
  have polarContinuous : Continuous polarIntegrand :=
    continuous_fst.mul (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp continuous_polarCoord_symm))
  have plainContinuous : Continuous (fun point : ℝ × ℝ =>
      function (spatialPlaneOfPair (polarCoord.symm point))) :=
    continuousFunction.comp (continuous_spatialPlaneOfPair.comp continuous_polarCoord_symm)
  have collarContinuous : Continuous (fun point : ℝ × ℝ => function (collarPlane point)) :=
    continuousFunction.comp collarPlane_smooth.continuous
  have pointwise (angle : ℝ) :
      (∫ radius in (0 : ℝ)..1, polarIntegrand (radius, angle)) ≤
        ∫ time in (0 : ℝ)..(1-lower), function (collarPlane (time, angle)) := by
    have polarSlice : Continuous (fun radius : ℝ => polarIntegrand (radius, angle)) := polarContinuous.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => angle)))
    have plainSlice : Continuous (fun radius : ℝ => function (spatialPlaneOfPair (polarCoord.symm (radius, angle)))) := plainContinuous.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => angle)))
    have zeroIntegral : (∫ radius in (0 : ℝ)..lower, polarIntegrand (radius, angle)) = 0 := by
      rw [intervalIntegral.integral_of_le positive.le]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius radiusIn
      have radiusBounds : 0 ≤ radius ∧ radius ≤ lower := ⟨radiusIn.1.le, radiusIn.2⟩
      change radius * function (spatialPlaneOfPair (polarCoord.symm (radius, angle))) = 0
      rw [vanishes _ ?_, mul_zero]
      have representation : spatialPlaneOfPair (polarCoord.symm (radius, angle)) = collarPlane (1 - radius, angle) := by
        rw [collarPlane_eq_polar, sub_sub_cancel]
      rw [representation, collarPlane_norm, sub_sub_cancel, abs_of_nonneg radiusBounds.1]
      exact radiusBounds.2
    rw [← intervalIntegral.integral_add_adjacent_intervals (polarSlice.intervalIntegrable 0 lower)
      (polarSlice.intervalIntegrable lower 1), zeroIntegral, zero_add]
    have comparison := intervalIntegral.integral_mono_on (μ := volume) bounded.le
      (polarSlice.intervalIntegrable _ _) (plainSlice.intervalIntegrable _ _)
      (fun radius radiusIn => mul_le_of_le_one_left (nonnegative _) radiusIn.2)
    apply comparison.trans_eq
    have substitution := intervalIntegral.integral_comp_sub_left
      (fun radius => function (spatialPlaneOfPair (polarCoord.symm (radius, angle))))
      (a := (0 : ℝ)) (b := (1-lower)) 1
    simpa only [sub_zero, show (1 : ℝ) - (1-lower) = lower by ring,
      ← collarPlane_eq_polar] using substitution.symm
  rw [closedUnitDisk_polar_integral function continuousFunction]
  unfold fixedCollarIntegral
  apply integral_mono
  · exact ((timeIntegral_continuous polarIntegrand polarContinuous 0 1 (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous _ collarContinuous 0 (1-lower) (by linarith)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact pointwise

end Grad.OriginalCollarNorm
