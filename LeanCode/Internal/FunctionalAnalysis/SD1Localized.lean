import SD1Density

noncomputable section

open MeasureTheory Filter Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues FieldL2)
open Grad.SpatialDilation (disk)
open scoped ContDiff Topology

namespace Grad.SmoothDensity

set_option maxHeartbeats 1600000

theorem localizedJet_base (dimension : ℕ) (innerRadius outerRadius : ℝ) (grade : Grade)
    (cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius))
    (jet : Jet dimension (disk outerRadius) grade) :
    jetBase dimension (disk outerRadius) grade (localizedJet dimension innerRadius outerRadius grade cutoff jet) =
      localizedField dimension innerRadius outerRadius cutoff (jetBase dimension (disk outerRadius) grade jet) :=
  cutoffMultiplier_base dimension (disk outerRadius) _ Metric.isOpen_ball cutoff grade jet

theorem localizedField_inner (dimension : ℕ) (innerRadius outerRadius : ℝ) (included : innerRadius ≤ outerRadius)
    (cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius))
    (field : FieldL2 dimension (disk outerRadius)) :
    Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
        (show disk innerRadius ⊆ disk outerRadius from Metric.ball_subset_ball included)
        (localizedField dimension innerRadius outerRadius cutoff field) =
      Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
        (show disk innerRadius ⊆ disk outerRadius from Metric.ball_subset_ball included) field :=
  restrict_scalar_field dimension (Metric.ball_subset_ball included) Metric.isOpen_ball.measurableSet
    Metric.isOpen_ball (Grad.CompactCutoff.boundedScalar cutoff (disk outerRadius))
    (fun _ inside => cutoff.one_on (Metric.ball_subset_closedBall inside)) field

theorem localizedJet_inner (dimension : ℕ) (innerRadius outerRadius : ℝ) (included : innerRadius ≤ outerRadius)
    (grade : Grade)
    (cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius))
    (jet : Jet dimension (disk outerRadius) grade) :
    innerRestriction dimension innerRadius outerRadius included grade
        (localizedJet dimension innerRadius outerRadius grade cutoff jet) =
      innerRestriction dimension innerRadius outerRadius included grade jet := by
  apply Grad.WeightedJets.base_injective dimension grade.order (disk innerRadius) Metric.isOpen_ball grade.exponent
  refine (Grad.WeightedJets.Restriction.restriction_base dimension grade.order (Metric.ball_subset_ball included)
    Metric.isOpen_ball.measurableSet grade.exponent _).trans ?_
  refine (congrArg (Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
    (show disk innerRadius ⊆ disk outerRadius from Metric.ball_subset_ball included))
    (localizedJet_base dimension innerRadius outerRadius grade cutoff jet)).trans ?_
  refine (localizedField_inner dimension innerRadius outerRadius included cutoff _).trans ?_
  exact (Grad.WeightedJets.Restriction.restriction_base dimension grade.order (Metric.ball_subset_ball included)
    Metric.isOpen_ball.measurableSet grade.exponent jet).symm

theorem localized_goal : LocalizedGoal := by
  intro dimension count innerRadius outerRadius nonnegativeInner strictRadii grades field jets sameBase
  let cutoff := radialCutoff innerRadius outerRadius nonnegativeInner strictRadii
  let localField := localizedField dimension innerRadius outerRadius cutoff field
  let localJets := fun index => localizedJet dimension innerRadius outerRadius (grades index) cutoff (jets index)
  have sameLocal : CommonBase dimension count outerRadius grades localField localJets := by
    intro index
    exact (localizedJet_base dimension innerRadius outerRadius (grades index) cutoff (jets index)).trans
      (congrArg (localizedField dimension innerRadius outerRadius cutoff) (sameBase index))
  obtain ⟨steps, scaleLimit, epsilonLimit, cellGrowth, smooth, rawLimit, limits⟩ :=
    density_goal dimension count outerRadius (nonnegativeInner.trans_lt strictRadii) grades localField localJets sameLocal
  have restrictedLocal := fun index =>
    localizedJet_inner dimension innerRadius outerRadius strictRadii.le (grades index) cutoff (jets index)
  refine ⟨cutoff, radialCutoff_laws innerRadius outerRadius nonnegativeInner strictRadii, sameLocal,
    restrictedLocal, steps, scaleLimit, epsilonLimit, cellGrowth, smooth,
    fun number index => (limits index).1 number, rawLimit, ?_, ?_⟩
  · let restriction := Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
      (show disk innerRadius ⊆ disk outerRadius from Metric.ball_subset_ball strictRadii.le)
    have limit := restriction.continuous.tendsto localField |>.comp rawLimit
    have composition : (fun number => restriction
        (Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk outerRadius))
          (stepField dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number) localField))) =
        (fun number => Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
          (Set.subset_univ (disk innerRadius))
          (stepField dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number) localField)) := by
      funext number
      exact congrArg (fun mapping => mapping
        (stepField dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number) localField))
        (Grad.WeightedJets.Restriction.fieldRestriction_comp (CellValues dimension)
          (Metric.ball_subset_ball strictRadii.le) (Set.subset_univ (disk outerRadius)))
    have value : restriction localField = restriction field :=
      localizedField_inner dimension innerRadius outerRadius strictRadii.le cutoff field
    change Tendsto (fun number => restriction
      (Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk outerRadius))
        (stepField dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number) localField)))
      atTop (𝓝 (restriction localField)) at limit
    rwa [composition, value] at limit
  · intro index
    refine ⟨(limits index).2, ?_⟩
    have limit := (innerRestriction dimension innerRadius outerRadius strictRadii.le (grades index)).continuous.tendsto
      (localJets index) |>.comp (limits index).2
    simpa only [Function.comp_def, localJets, localizedJet_inner] using limit

end Grad.SmoothDensity
