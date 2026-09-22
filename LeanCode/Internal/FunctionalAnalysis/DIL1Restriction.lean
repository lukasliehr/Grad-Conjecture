import DIL1Jet
import DIL1Continuous

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets
open scoped BigOperators Topology

namespace Grad.SpatialDilation

theorem restrictedRaw_plane_extension (dimension : ℕ) (radius : ℝ) (scale : Scale)
    (field : FieldL2 dimension (disk radius)) :
    restrictedRaw dimension radius scale field =
      Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))
        (rawValue dimension Set.univ MeasurableSet.univ scale
          (ZeroExtension.fieldExtension (CellValues dimension) (disk radius) Metric.isOpen_ball.measurableSet field)) := by
  apply Lp.ext
  let extension := ZeroExtension.fieldExtension (CellValues dimension) (disk radius)
    Metric.isOpen_ball.measurableSet field
  filter_upwards [Restriction.fieldRestriction_ae (CellValues dimension) (disk_subset_expanded radius scale)
      (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale field),
    Restriction.fieldRestriction_ae (CellValues dimension) (Set.subset_univ (disk radius))
      (rawValue dimension Set.univ MeasurableSet.univ scale extension),
    ae_restrict_of_ae_restrict_of_subset (disk_subset_expanded radius scale)
      (rawValue_ae dimension (disk radius) Metric.isOpen_ball.measurableSet scale field),
    ae_restrict_of_ae_restrict_of_subset (Set.subset_univ (disk radius))
      (rawValue_ae dimension Set.univ MeasurableSet.univ scale extension),
    ae_restrict_of_ae_restrict_of_subset (disk_subset_expanded radius scale)
      (pull_ae (disk radius) Metric.isOpen_ball.measurableSet scale
        (ZeroExtension.fieldExtension_inside (CellValues dimension) (disk radius) Metric.isOpen_ball.measurableSet field))]
    with point first second rawFirst rawSecond extended
  exact first.trans (rawFirst.trans (extended.symm.trans (rawSecond.symm.trans second.symm)))

theorem restrictedRaw_tendsto (dimension : ℕ) (radius : ℝ) (field : FieldL2 dimension (disk radius)) :
    Filter.Tendsto (fun scale : Scale => restrictedRaw dimension radius scale field) (𝓝 oneScale) (𝓝 field) := by
  have limit := (Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))).continuous.continuousAt.tendsto.comp
    (plane_continuity_goal dimension
      (ZeroExtension.fieldExtension (CellValues dimension) (disk radius) Metric.isOpen_ball.measurableSet field))
  have represented := limit.congr' (Filter.Eventually.of_forall (fun scale : Scale =>
    (restrictedRaw_plane_extension dimension radius scale field).symm))
  simpa only [ZeroExtension.restriction_extension (CellValues dimension) (disk radius)
    Metric.isOpen_ball.measurableSet field] using represented

theorem raw_restriction_goal : RawRestrictionGoal := by
  intro dimension radius field
  exact ⟨fun scale => restrictedRaw_plane_extension dimension radius scale field,
    restrictedRaw_tendsto dimension radius field⟩

theorem restricted_jet_coordinate (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) (index : JetIndex order) :
    (restrictExpanded dimension order radius scale exponent (jetDilation dimension order radius scale exponent jet)).val index =
      (scale.val ^ degree index : ℂ) • restrictedRaw dimension radius scale (jet.val index) :=
  map_smul (Restriction.fieldRestriction (CellValues dimension) (disk_subset_expanded radius scale))
    (scale.val ^ degree index : ℂ)
    (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (jet.val index))

theorem restricted_jet_coordinate_tendsto (dimension order : ℕ) (radius : ℝ)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order (disk radius) exponent) (index : JetIndex order) :
    Filter.Tendsto (fun scale : Scale =>
      (restrictExpanded dimension order radius scale exponent (jetDilation dimension order radius scale exponent jet)).val index)
      (𝓝 oneScale) (𝓝 (jet.val index)) := by
  have scalar : Filter.Tendsto (fun scale : Scale => (scale.val ^ degree index : ℂ)) (𝓝 oneScale) (𝓝 1) := by
    simpa only [Function.comp_def, show oneScale.val = (1 : ℝ) from rfl, Complex.ofReal_one, one_pow] using
      (((Complex.continuous_ofReal.comp continuous_scale_val).tendsto oneScale).pow (degree index))
  have limit := scalar.smul (restrictedRaw_tendsto dimension radius (jet.val index))
  simpa only [← restricted_jet_coordinate, one_smul] using limit

theorem restricted_jet_tendsto (dimension order : ℕ) (radius : ℝ) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order (disk radius) exponent) :
    Filter.Tendsto (fun scale : Scale => restrictExpanded dimension order radius scale exponent
      (jetDilation dimension order radius scale exponent jet)) (𝓝 oneScale) (𝓝 jet) := by
  have each (index : JetIndex order) :=
    ((restricted_jet_coordinate_tendsto dimension order radius exponent jet index).sub_const (jet.val index)).norm.pow 2
  have squared : Filter.Tendsto (fun scale : Scale =>
      ‖restrictExpanded dimension order radius scale exponent (jetDilation dimension order radius scale exponent jet) - jet‖ ^ 2)
      (𝓝 oneScale) (𝓝 0) := by
    have sumLimit := tendsto_finsetSum Finset.univ (fun index _membership => each index)
    simpa only [jet_norm_sq, Submodule.coe_sub, PiLp.sub_apply, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using sumLimit
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have limit := Real.continuous_sqrt.continuousAt.tendsto.comp squared
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using limit

theorem restrictedRaw_one (dimension : ℕ) (radius : ℝ) (field : FieldL2 dimension (disk radius)) :
    restrictedRaw dimension radius oneScale field = field := by
  rw [restrictedRaw_plane_extension, rawValue_plane_one]
  exact ZeroExtension.restriction_extension (CellValues dimension) (disk radius) Metric.isOpen_ball.measurableSet field

theorem restricted_jet_one (dimension order : ℕ) (radius : ℝ) (exponent : JetIndex order → ℕ) :
    (restrictExpanded dimension order radius oneScale exponent).comp (jetDilation dimension order radius oneScale exponent) =
      ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro jet
  apply jet_eq
  intro index
  change (restrictExpanded dimension order radius oneScale exponent
    (jetDilation dimension order radius oneScale exponent jet)).val index = jet.val index
  rw [restricted_jet_coordinate, restrictedRaw_one]
  simp only [oneScale, Complex.ofReal_one, one_pow, one_smul]

theorem jet_goal : JetGoal := by
  intro dimension order radius exponent
  exact ⟨fun scale => jetDilation dimension order radius scale exponent,
    fun scale => jetDilation_laws dimension order radius scale exponent,
    restricted_jet_tendsto dimension order radius exponent,
    restricted_jet_one dimension order radius exponent⟩

end Grad.SpatialDilation
