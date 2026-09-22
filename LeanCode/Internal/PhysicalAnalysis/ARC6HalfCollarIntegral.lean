import ARC5FiniteTensorRows
import BL23OriginalCell

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift
open Grad.DiskExtension.Operator

def halfCollarRectangle : Set (ℝ × ℝ) := Icc (0 : ℝ) (1 / 2) ×ˢ Icc (-Real.pi) Real.pi

def halfCollarIntegral (function : ℝ × ℝ → ℝ) : ℝ :=
  ∫ angle in Ioo (-Real.pi) Real.pi, ∫ time in (0 : ℝ)..(1 / 2 : ℝ), function (time, angle)

theorem halfCollarIntegral_mono (first second : ℝ × ℝ → ℝ)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (bound : ∀ point ∈ halfCollarRectangle, first point ≤ second point) :
    halfCollarIntegral first ≤ halfCollarIntegral second := by
  apply integral_mono_ae
  · exact ((timeIntegral_continuous first firstContinuous 0 (1 / 2) (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous second secondContinuous 0 (1 / 2) (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with angle angleIn
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2)
    · exact (firstContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact (secondContinuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · intro time timeIn
      exact bound (time, angle) ⟨timeIn, ⟨angleIn.1.le, angleIn.2.le⟩⟩

theorem halfCollarIntegral_const_mul (scalar : ℝ) (function : ℝ × ℝ → ℝ) :
    halfCollarIntegral (fun point => scalar * function point) = scalar * halfCollarIntegral function := by
  unfold halfCollarIntegral
  simp only [intervalIntegral.integral_const_mul, integral_const_mul]

theorem halfCollarIntegral_swap (function : ℝ × ℝ → ℝ) (continuousFunction : Continuous function) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ∫ angle in -Real.pi..Real.pi, function (time, angle)) =
      halfCollarIntegral function := by
  have integrable : Integrable function
      ((volume.restrict (Icc (0 : ℝ) (1 / 2))).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact continuousFunction.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have swap := integral_integral_swap (f := fun time angle : ℝ => function (time, angle)) integrable
  unfold halfCollarIntegral
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp_rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact swap

theorem disk_integral_le_halfCollar (function : SpatialPlane → ℝ) (continuousFunction : Continuous function)
    (nonnegative : ∀ point, 0 ≤ function point)
    (vanishes : ∀ point, ‖point‖ ≤ (1 / 2 : ℝ) → function point = 0) :
    (∫ point in closedUnitDisk, function point) ≤
      halfCollarIntegral (fun point => function (collarPlane point)) := by
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
        ∫ time in (0 : ℝ)..(1 / 2 : ℝ), function (collarPlane (time, angle)) := by
    have polarSlice : Continuous (fun radius : ℝ => polarIntegrand (radius, angle)) := polarContinuous.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => angle)))
    have plainSlice : Continuous (fun radius : ℝ => function (spatialPlaneOfPair (polarCoord.symm (radius, angle)))) := plainContinuous.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => angle)))
    have zeroIntegral : (∫ radius in (0 : ℝ)..(1 / 2 : ℝ), polarIntegrand (radius, angle)) = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius radiusIn
      have radiusBounds : 0 ≤ radius ∧ radius ≤ (1 / 2 : ℝ) := ⟨radiusIn.1.le, radiusIn.2⟩
      change radius * function (spatialPlaneOfPair (polarCoord.symm (radius, angle))) = 0
      rw [vanishes _ ?_, mul_zero]
      have representation : spatialPlaneOfPair (polarCoord.symm (radius, angle)) = collarPlane (1 - radius, angle) := by
        rw [collarPlane_eq_polar, sub_sub_cancel]
      rw [representation, collarPlane_norm, sub_sub_cancel, abs_of_nonneg radiusBounds.1]
      exact radiusBounds.2
    rw [← intervalIntegral.integral_add_adjacent_intervals (polarSlice.intervalIntegrable 0 (1 / 2))
      (polarSlice.intervalIntegrable (1 / 2) 1), zeroIntegral, zero_add]
    have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (polarSlice.intervalIntegrable _ _) (plainSlice.intervalIntegrable _ _)
      (fun radius radiusIn => mul_le_of_le_one_left (nonnegative _) radiusIn.2)
    apply comparison.trans_eq
    have substitution := intervalIntegral.integral_comp_sub_left
      (fun radius => function (spatialPlaneOfPair (polarCoord.symm (radius, angle))))
      (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) 1
    simpa only [sub_zero, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      ← collarPlane_eq_polar] using substitution.symm
  rw [closedUnitDisk_polar_integral function continuousFunction]
  unfold halfCollarIntegral
  apply integral_mono
  · exact ((timeIntegral_continuous polarIntegrand polarContinuous 0 1 (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous _ collarContinuous 0 (1 / 2) (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact pointwise

theorem halfCollarIntegral_nonnegative (function : ℝ × ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ function point) :
    0 ≤ halfCollarIntegral function := by
  apply integral_nonneg
  intro angle
  exact intervalIntegral.integral_nonneg (by norm_num) (fun time _ => nonnegative (time, angle))

theorem halfCollarIntegral_finsetSum {Index : Type*} (indices : Finset Index) (functions : Index → ℝ × ℝ → ℝ)
    (continuousFunctions : ∀ index ∈ indices, Continuous (functions index)) :
    halfCollarIntegral (fun point => ∑ index ∈ indices, functions index point) =
      ∑ index ∈ indices, halfCollarIntegral (functions index) := by
  unfold halfCollarIntegral
  have inner (angle : ℝ) : (∫ time in (0 : ℝ)..(1 / 2 : ℝ),
      ∑ index ∈ indices, functions index (time, angle)) =
      ∑ index ∈ indices, ∫ time in (0 : ℝ)..(1 / 2 : ℝ), functions index (time, angle) := by
    apply intervalIntegral.integral_finsetSum
    intro index member
    have continuousSlice : Continuous (fun time : ℝ => functions index (time, angle)) :=
      (continuousFunctions index member).comp (continuous_id.prodMk continuous_const)
    exact continuousSlice.intervalIntegrable _ _
  simp_rw [inner]
  rw [integral_finsetSum]
  intro index member
  exact ((timeIntegral_continuous (functions index) (continuousFunctions index member) 0 (1 / 2)
    (by norm_num)).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self


end Grad.CollarCartesian
