import BT6OriginalDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.DiskExtension.Operator

theorem timeIntegral_continuous (function : ℝ × ℝ → ℝ) (continuousFunction : Continuous function)
    (left right : ℝ) (ordered : left ≤ right) :
    Continuous (fun angle : ℝ => ∫ time in left..right, function (time, angle)) := by
  have compactIntegral := continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ))
    (f := fun angle time : ℝ => function (time, angle))
    (continuousFunction.comp continuous_swap) (s := Icc left right) isCompact_Icc
  have equality : (fun angle : ℝ => ∫ time in left..right, function (time, angle)) =
      fun angle : ℝ => ∫ time in Icc left right, function (time, angle) := by
    funext angle
    rw [intervalIntegral.integral_of_le ordered, integral_Icc_eq_integral_Ioc]
  rwa [equality]

theorem closedUnitDisk_ae_openUnitDisk : closedUnitDisk =ᵐ[(volume : Measure SpatialPlane)] openUnitDisk := by
  have avoidSphere : ∀ᵐ point : SpatialPlane, point ∉ Metric.sphere (0 : SpatialPlane) 1 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using Measure.addHaar_sphere (volume : Measure SpatialPlane) 0 1
  filter_upwards [avoidSphere] with point offSphere
  have normNe : ‖point‖ ≠ 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using offSphere
  apply propext
  change (‖point‖ ≤ 1 ↔ ‖point‖ < 1)
  exact ⟨fun bound => lt_of_le_of_ne bound normNe, fun bound => bound.le⟩

theorem collarPlane_eq_polar (time angle : ℝ) :
    collarPlane (time, angle) = spatialPlaneOfPair (polarCoord.symm (1 - time, angle)) := rfl

theorem collar_integral_le_disk (function : SpatialPlane → ℝ) (continuousFunction : Continuous function)
    (nonnegative : ∀ point, 0 ≤ function point) :
    (∫ angle in Ioo (-Real.pi) Real.pi,
      ∫ time in (0 : ℝ)..(1 / 4 : ℝ), function (collarPlane (time, angle))) ≤
      (4 / 3 : ℝ) * ∫ point in closedUnitDisk, function point := by
  let polarIntegrand : ℝ × ℝ → ℝ := fun point =>
    point.1 * function (spatialPlaneOfPair (polarCoord.symm point))
  have polarContinuous : Continuous polarIntegrand :=
    continuous_fst.mul (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp continuous_polarCoord_symm))
  have collarContinuous : Continuous (fun point : ℝ × ℝ => function (collarPlane point)) :=
    continuousFunction.comp collarPlane_smooth.continuous
  have pointwise : ∀ angle : ℝ,
      (∫ time in (0 : ℝ)..(1 / 4 : ℝ), function (collarPlane (time, angle))) ≤
        (4 / 3 : ℝ) * ∫ radius in (0 : ℝ)..1, polarIntegrand (radius, angle) := by
    intro angle
    have innerComparison := intervalIntegral.integral_mono_on (μ := volume)
      (f := fun time : ℝ => function (collarPlane (time, angle)))
      (g := fun time : ℝ => (4 / 3 : ℝ) * ((1 - time) * function (collarPlane (time, angle))))
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      ((collarContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 (1 / 4))
      ((continuous_const.mul ((continuous_const.sub continuous_id).mul
        (collarContinuous.comp (continuous_id.prodMk continuous_const)))).intervalIntegrable 0 (1 / 4))
      (fun time timeIn => by
        have functionNonnegative := nonnegative (collarPlane (time, angle))
        have timeUpper := timeIn.2
        nlinarith [mul_nonneg (by linarith : 0 ≤ (1 / 4 : ℝ) - time) functionNonnegative])
    change (∫ time in (0 : ℝ)..(1 / 4 : ℝ), function (collarPlane (time, angle))) ≤
      ∫ time in (0 : ℝ)..(1 / 4 : ℝ),
        (4 / 3 : ℝ) * ((1 - time) * function (collarPlane (time, angle))) at innerComparison
    rw [intervalIntegral.integral_const_mul] at innerComparison
    have substitution : (∫ time in (0 : ℝ)..(1 / 4 : ℝ),
        (1 - time) * function (collarPlane (time, angle))) =
        ∫ radius in (3 / 4 : ℝ)..1, polarIntegrand (radius, angle) := by
      change (∫ time in (0 : ℝ)..(1 / 4 : ℝ), polarIntegrand (1 - time, angle)) = _
      convert intervalIntegral.integral_comp_sub_left
        (fun radius => polarIntegrand (radius, angle)) (a := (0 : ℝ)) (b := (1 / 4 : ℝ)) 1 using 1
      norm_num
    rw [substitution] at innerComparison
    apply innerComparison.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4 / 3)
    apply intervalIntegral.integral_mono_interval (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) ≤ 1) le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius radiusIn
      exact mul_nonneg radiusIn.1.le (nonnegative _)
    · exact (polarContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
  rw [closedUnitDisk_polar_integral function continuousFunction, ← integral_const_mul]
  apply integral_mono
  · exact ((timeIntegral_continuous _ collarContinuous 0 (1 / 4) (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((continuous_const.mul (timeIntegral_continuous polarIntegrand polarContinuous 0 1 (by norm_num))).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact pointwise

end Grad.BoundaryTrace
