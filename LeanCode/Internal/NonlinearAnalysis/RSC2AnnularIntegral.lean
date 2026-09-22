import RSC1PolarDensity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarRestriction

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarDivision Grad.DiskExtension.Operator

theorem polarPlane_polar (radius angle : ℝ) :
    polarPlane (radius, angle) = spatialPlaneOfPair (polarCoord.symm (radius, angle)) := by
  simp only [polarPlane, collarPlane_eq_polar, sub_sub_cancel]

/-- The physical polar area measure, with its radial Jacobian retained. -/
def annularIntegral (lower : ℝ) (field : ℝ × ℝ → ℝ) : ℝ :=
  ∫ angle in Ioo (-Real.pi) Real.pi, ∫ radius in lower..1, radius * field (radius, angle)

theorem annularIntegral_const_mul (lower scalar : ℝ) (field : ℝ × ℝ → ℝ) :
    annularIntegral lower (fun point => scalar * field point) = scalar * annularIntegral lower field := by
  unfold annularIntegral
  simp_rw [mul_left_comm _ scalar, intervalIntegral.integral_const_mul, integral_const_mul]

theorem annularIntegral_mono (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (first second : ℝ × ℝ → ℝ) (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (bound : ∀ point ∈ polarRectangle, first point ≤ second point) :
    annularIntegral lower first ≤ annularIntegral lower second := by
  have firstWeighted := continuous_fst.mul firstContinuous
  have secondWeighted := continuous_fst.mul secondContinuous
  apply integral_mono_ae
  · exact ((timeIntegral_continuous _ firstWeighted lower 1 bounded).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous _ secondWeighted lower 1 bounded).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with angle angleIn
    apply intervalIntegral.integral_mono_on bounded
    · exact (firstWeighted.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · exact (secondWeighted.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    · intro radius radiusIn
      exact mul_le_mul_of_nonneg_left
        (bound (radius, angle) ⟨⟨nonnegative.trans radiusIn.1, radiusIn.2⟩, angleIn.1.le, angleIn.2.le⟩)
        (nonnegative.trans radiusIn.1)

theorem annularIntegral_swap (lower : ℝ) (bounded : lower ≤ 1)
    (field : ℝ × ℝ → ℝ) (continuousField : Continuous field) :
    (∫ radius in lower..1, radius * ∫ angle in -Real.pi..Real.pi, field (radius, angle)) =
      annularIntegral lower field := by
  have weighted := continuous_fst.mul continuousField
  have integrable : Integrable (fun point : ℝ × ℝ => point.1 * field point)
      ((volume.restrict (Icc lower 1)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact weighted.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have swap := integral_integral_swap (f := fun radius angle : ℝ => radius * field (radius, angle)) integrable
  simp_rw [← intervalIntegral.integral_const_mul]
  unfold annularIntegral
  simp_rw [intervalIntegral.integral_of_le bounded,
    intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simp_rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact swap

/-- Restricting the exact polar area integral incurs no power of the inner radius. -/
theorem annularIntegral_le_disk (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1)
    (field : SpatialPlane → ℝ) (continuousField : Continuous field)
    (fieldNonnegative : ∀ point, 0 ≤ field point) :
    annularIntegral lower (field ∘ polarPlane) ≤ ∫ point in closedUnitDisk, field point := by
  have weighted : Continuous (fun point : ℝ × ℝ => point.1 * field (polarPlane point)) :=
    continuous_fst.mul (continuousField.comp polarPlane_smooth.continuous)
  rw [closedUnitDisk_polar_integral field continuousField]
  simp_rw [← polarPlane_polar]
  apply integral_mono
  · exact ((timeIntegral_continuous _ weighted lower 1 bounded).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous _ weighted 0 1 (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · intro angle
    change (∫ radius in lower..1, radius * field (polarPlane (radius, angle))) ≤
      ∫ radius in (0 : ℝ)..1, radius * field (polarPlane (radius, angle))
    apply intervalIntegral.integral_mono_interval nonnegative bounded le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius radiusIn
      exact mul_nonneg radiusIn.1.le (fieldNonnegative _)
    · exact (weighted.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _

theorem original_polar_mixed_integral_bound {dimension grade radial angular power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : angular + radial + power ≤ grade)
    (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower ≤ 1) :
    cellFrequency cell ^ (2 * power) * annularIntegral lower (fun point =>
      ‖angularJet angular (radialIter radial (originalPolarValue (phaseWeightedJet parameters cell field))) point‖ ^ 2) ≤
      polarOrderConstant (angular + radial) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 := by
  let polar := originalPolarValue (phaseWeightedJet parameters cell field)
  let density := cartesianDensityGlobal (cellFrequency cell) grade (phaseWeightedJet parameters cell field)
  have jetContinuous : Continuous (fun point => ‖angularJet angular (radialIter radial polar) point‖ ^ 2) :=
    (angularJet_smooth angular _ (radialIter_smooth radial polar (originalPolarValue_smooth _))).continuous.norm.pow 2
  have densityContinuous : Continuous density := cartesianDensityGlobal_continuous _ _ _
  have comparison := annularIntegral_mono lower nonnegative bounded
    (fun point => cellFrequency cell ^ (2 * power) * ‖angularJet angular (radialIter radial polar) point‖ ^ 2)
    (fun point => polarOrderConstant (angular + radial) * density (polarPlane point))
    (continuous_const.mul jetContinuous)
    (continuous_const.mul (densityContinuous.comp polarPlane_smooth.continuous))
    (weighted_polar_mixed_sq_le_density parameters cell field paid)
  rw [annularIntegral_const_mul, annularIntegral_const_mul] at comparison
  have area := annularIntegral_le_disk lower nonnegative bounded density densityContinuous
    (fun point => cartesianPointDensity_nonnegative _ (cellFrequency_pos cell).le _ _ _)
  rw [cartesianDensityGlobal_integral_original parameters cell field] at area
  exact comparison.trans (mul_le_mul_of_nonneg_left area (polarOrderConstant_nonnegative _))

end Grad.SourceCollarRestriction
