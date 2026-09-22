import SD1Stage

noncomputable section

open MeasureTheory Filter Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.SpatialDilation (Scale disk expandedDisk diskMargin)
open scoped ContDiff Topology BigOperators

namespace Grad.SmoothDensity

set_option maxHeartbeats 1600000

def seedStep (radius : ℝ) (positiveRadius : 0 < radius) (scale : Scale) (strict : scale.val < 1) : Step radius where
  scale := scale
  strict := strict
  epsilon := diskMargin radius scale / 4
  positiveEpsilon := div_pos (Grad.SpatialDilation.geometry_goal.2 radius scale positiveRadius strict).1 (by norm_num)
  smallEpsilon := by have positive := (Grad.SpatialDilation.geometry_goal.2 radius scale positiveRadius strict).1; linarith
  cellRadius := 0

theorem finite_choice_goal : FiniteChoiceGoal := by
  intro dimension count radius positiveRadius grades jets scale strict tolerance positiveTolerance minimumCells
  let initial := seedStep radius positiveRadius scale strict
  let extended := fun index => extendedJet dimension radius positiveRadius (grades index) initial (jets index)
  have allErrors : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), ∀ index : Fin count,
      ‖Grad.Mollifier.WeakJets.Consumer.weightedRegularizer dimension (grades index).order
        (grades index).exponent epsilon (extended index) - extended index‖ < tolerance := by
    apply Filter.eventually_all.mpr
    intro index
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp
      (Grad.Mollifier.WeakJets.Consumer.weightedStrongApproximation
        dimension (grades index).order (grades index).exponent (extended index)) tolerance positiveTolerance)
  have positiveMargin := (Grad.SpatialDilation.geometry_goal.2 radius scale positiveRadius strict).1
  have small : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), epsilon < min tolerance (diskMargin radius scale / 2) :=
    (show ∀ᶠ epsilon in 𝓝 (0 : ℝ), epsilon < min tolerance (diskMargin radius scale / 2) from
      Iio_mem_nhds (lt_min positiveTolerance (half_pos positiveMargin))).filter_mono nhdsWithin_le_nhds
  have positive : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < epsilon := self_mem_nhdsWithin
  obtain ⟨epsilon, positiveEpsilon, smallEpsilon, regularizerErrors⟩ := (positive.and (small.and allErrors)).exists
  let candidate : Step radius := ⟨scale, strict, epsilon, positiveEpsilon, smallEpsilon.trans_le (min_le_right _ _), 0⟩
  let regularized := fun index => regularizedJet dimension radius positiveRadius (grades index) candidate (jets index)
  have cellErrors : ∀ᶠ number : ℕ in atTop, ∀ index : Fin count,
      ‖Grad.WeightedJets.CellCutoff.cutoff dimension (grades index).order Set.univ (grades index).exponent
        (Grad.WeightedJets.CellCutoff.centeredCells number) (regularized index) - regularized index‖ < tolerance := by
    apply Filter.eventually_all.mpr
    intro index
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp
      (Grad.WeightedJets.CellCutoff.cutoff_sequence_strong dimension (grades index).order Set.univ
        (grades index).exponent (regularized index)) tolerance positiveTolerance
  obtain ⟨number, enoughCells, cutoffErrors⟩ := ((eventually_ge_atTop minimumCells).and cellErrors).exists
  refine ⟨{ candidate with cellRadius := number }, rfl, smallEpsilon.trans_le (min_le_left _ _), enoughCells, ?_⟩
  intro index
  exact ⟨regularizerErrors index, cutoffErrors index⟩

theorem restrict_extension_field (dimension : ℕ) {smaller larger : Set Spatial}
    (inclusion : smaller ⊆ larger) (measurable : MeasurableSet larger) (field : FieldL2 dimension larger) :
    Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ smaller)
        (Grad.WeightedJets.ZeroExtension.fieldExtension (CellValues dimension) larger measurable field) =
      Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) inclusion field := by
  apply Lp.ext
  have interior : Grad.WeightedJets.ZeroExtension.fieldExtension (CellValues dimension) larger measurable field
      =ᵐ[volume.restrict smaller] field :=
    ae_mono (Measure.restrict_mono inclusion le_rfl)
      (Grad.WeightedJets.ZeroExtension.fieldExtension_inside (CellValues dimension) larger measurable field)
  exact (Grad.WeightedJets.Restriction.fieldRestriction_ae (CellValues dimension) (Set.subset_univ smaller) _).trans
    (interior.trans (Grad.WeightedJets.Restriction.fieldRestriction_ae (CellValues dimension) inclusion field).symm)

theorem restrict_scalar_field (dimension : ℕ) {smaller larger : Set Spatial}
    (inclusion : smaller ⊆ larger) (measurable : MeasurableSet smaller) (openLarger : IsOpen larger)
    (scalar : Grad.WeightedJets.SpatialMultiplier.BoundedScalar larger)
    (oneOn : Set.EqOn scalar.toFun (fun _ => 1) smaller) (field : FieldL2 dimension larger) :
    Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) inclusion
        (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension larger openLarger scalar field) =
      Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) inclusion field := by
  apply Lp.ext
  filter_upwards [Grad.WeightedJets.Restriction.fieldRestriction_ae (CellValues dimension) inclusion
      (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension larger openLarger scalar field),
    Grad.WeightedJets.Restriction.fieldRestriction_ae (CellValues dimension) inclusion field,
    ae_mono (Measure.restrict_mono inclusion le_rfl)
      (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier_ae dimension larger openLarger scalar field),
    ae_restrict_mem measurable] with point leftAt rightAt multipliedAt inside
  rw [leftAt, rightAt]
  apply lp.ext
  funext cell
  rw [multipliedAt cell, oneOn inside, Complex.ofReal_one, one_smul]

theorem restrict_preparedField (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) :
    Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))
        (preparedField dimension radius positiveRadius step field) =
      Grad.SpatialDilation.restrictedRaw dimension radius step.scale field := by
  unfold preparedField
  refine (restrict_extension_field dimension (Grad.SpatialDilation.disk_subset_expanded radius step.scale)
    (Grad.SpatialDilation.expandedDisk_open radius step.scale).measurableSet _).trans ?_
  apply restrict_scalar_field dimension _ Metric.isOpen_ball.measurableSet
  intro point inside
  exact (collar radius positiveRadius step.scale step.strict).one_on (Metric.ball_subset_closedBall inside)

theorem restrict_extendedJet (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) (jet : Jet dimension (disk radius) grade) :
    restrictJet dimension radius grade (extendedJet dimension radius positiveRadius grade step jet) =
      Grad.SpatialDilation.restrictExpanded dimension grade.order radius step.scale grade.exponent
        (Grad.SpatialDilation.jetDilation dimension grade.order radius step.scale grade.exponent jet) := by
  apply Grad.WeightedJets.base_injective dimension grade.order (disk radius) Metric.isOpen_ball grade.exponent
  refine (Grad.WeightedJets.Restriction.restriction_base dimension grade.order (Set.subset_univ (disk radius))
    MeasurableSet.univ grade.exponent _).trans ?_
  refine (congrArg (Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius)))
    (extendedJet_base dimension radius positiveRadius grade step jet)).trans ?_
  refine (restrict_preparedField dimension radius positiveRadius step _).trans ?_
  symm
  refine (Grad.WeightedJets.Restriction.restriction_base dimension grade.order
    (Grad.SpatialDilation.disk_subset_expanded radius step.scale)
    (Grad.SpatialDilation.expandedDisk_open radius step.scale).measurableSet grade.exponent _).trans ?_
  exact congrArg (Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
    (Grad.SpatialDilation.disk_subset_expanded radius step.scale))
    (Grad.SpatialDilation.jetDilation_base dimension grade.order radius step.scale grade.exponent jet)

def tolerance (number : ℕ) : ℝ := 1 / ((number : ℝ) + 1)

theorem tolerance_positive (number : ℕ) : 0 < tolerance number := by unfold tolerance; positivity

theorem tolerance_tendsto : Tendsto tolerance atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

def approachScale (number : ℕ) : Scale :=
  ⟨((number : ℝ) + 1) / ((number : ℝ) + 2), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr; linarith⟩

theorem approachScale_strict (number : ℕ) : (approachScale number).val < 1 := by
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem approachScale_tendsto : Tendsto approachScale atTop (𝓝 Grad.SpatialDilation.oneScale) := by
  apply tendsto_subtype_rng.mpr
  have inverseLimit : Tendsto (fun number : ℕ => 1 / ((number : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, tolerance, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (tolerance_tendsto.comp (Filter.tendsto_add_atTop_nat 1))
  have difference := (tendsto_const_nhds (x := (1 : ℝ))).sub inverseLimit
  convert difference using 1
  · funext number
    change ((number : ℝ) + 1) / ((number : ℝ) + 2) = 1 - 1 / ((number : ℝ) + 2)
    field_simp
    ring
  · norm_num [Grad.SpatialDilation.oneScale]

theorem approximation_tendsto (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (jet : Jet dimension (disk radius) grade) (steps : ℕ → Step radius)
    (scaleLimit : Tendsto (fun number => (steps number).scale) atTop (𝓝 Grad.SpatialDilation.oneScale))
    (errors : ∀ number,
      ‖regularizedJet dimension radius positiveRadius grade (steps number) jet -
        extendedJet dimension radius positiveRadius grade (steps number) jet‖ < tolerance number ∧
      ‖stepJet dimension radius positiveRadius grade (steps number) jet -
        regularizedJet dimension radius positiveRadius grade (steps number) jet‖ < tolerance number) :
    Tendsto (fun number => restrictJet dimension radius grade
      (stepJet dimension radius positiveRadius grade (steps number) jet)) atTop (𝓝 jet) := by
  have errorLimit : Tendsto (fun number => stepJet dimension radius positiveRadius grade (steps number) jet -
      extendedJet dimension radius positiveRadius grade (steps number) jet) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun number => (norm_sub_le_norm_sub_add_norm_sub _
        (regularizedJet dimension radius positiveRadius grade (steps number) jet) _).trans
        (add_le_add (errors number).2.le (errors number).1.le))
    simpa only [zero_add] using tolerance_tendsto.add tolerance_tendsto
  have extendedLimit : Tendsto (fun number => restrictJet dimension radius grade
      (extendedJet dimension radius positiveRadius grade (steps number) jet)) atTop (𝓝 jet) := by
    simp_rw [restrict_extendedJet]
    exact (Grad.SpatialDilation.restricted_jet_tendsto dimension grade.order radius grade.exponent jet).comp scaleLimit
  have result := ((restrictJet dimension radius grade).continuous.tendsto 0 |>.comp errorLimit).add extendedLimit
  simpa only [Function.comp_def, map_sub, map_zero, zero_add, sub_add_cancel] using result

end Grad.SmoothDensity
