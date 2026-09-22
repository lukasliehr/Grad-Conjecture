import SD1Approximation

noncomputable section

open MeasureTheory Filter Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues FieldL2)
open Grad.SpatialDilation (disk)
open scoped ContDiff Topology

namespace Grad.SmoothDensity

set_option maxHeartbeats 1600000

theorem restrict_stepJet_base (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) (jet : Jet dimension (disk radius) grade) :
    jetBase dimension (disk radius) grade
        (restrictJet dimension radius grade (stepJet dimension radius positiveRadius grade step jet)) =
      Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))
        (stepField dimension radius positiveRadius step (jetBase dimension (disk radius) grade jet)) :=
  (Grad.WeightedJets.Restriction.restriction_base dimension grade.order (Set.subset_univ (disk radius))
    MeasurableSet.univ grade.exponent _).trans
    (congrArg (Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius)))
      (stepJet_base dimension radius positiveRadius grade step jet))

theorem density_goal : DensityGoal := by
  intro dimension count radius positiveRadius grades field jets sameBase
  let allGrades : Fin (count + 1) → Grade := Fin.cases (.graph 0 0) grades
  let allJets : ∀ index, Jet dimension (disk radius) (allGrades index) :=
    Fin.cases (rawZeroJet dimension (disk radius) field) jets
  have witnesses (number : ℕ) := finite_choice_goal dimension (count + 1) radius positiveRadius allGrades allJets
    (approachScale number) (approachScale_strict number) (tolerance number) (tolerance_positive number) number
  let steps : ℕ → Step radius := fun number => (witnesses number).choose
  have properties (number : ℕ) := (witnesses number).choose_spec
  have scaleLimit : Tendsto (fun number => (steps number).scale) atTop (𝓝 Grad.SpatialDilation.oneScale) := by
    have equality : (fun number => (steps number).scale) = approachScale := funext (fun number => (properties number).1)
    rw [equality]
    exact approachScale_tendsto
  have epsilonLimit : Tendsto (fun number => (steps number).epsilon) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_inf.mpr
    refine ⟨squeeze_zero (fun number => (steps number).positiveEpsilon.le)
      (fun number => (properties number).2.1.le) tolerance_tendsto, ?_⟩
    exact tendsto_principal.mpr (Eventually.of_forall (fun number => (steps number).positiveEpsilon))
  have limits (index : Fin (count + 1)) := approximation_tendsto dimension radius positiveRadius (allGrades index)
    (allJets index) steps scaleLimit (fun number => (properties number).2.2.2 index)
  have zeroLimit : Tendsto (fun number => restrictJet dimension radius (.graph 0 0)
      (stepJet dimension radius positiveRadius (.graph 0 0) (steps number) (rawZeroJet dimension (disk radius) field)))
      atTop (𝓝 (rawZeroJet dimension (disk radius) field)) := limits 0
  have rawLimit : Tendsto (fun number =>
      Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))
        (stepField dimension radius positiveRadius (steps number) field)) atTop (𝓝 field) := by
    have limit := (jetBase dimension (disk radius) (.graph 0 0)).continuous.tendsto
      (rawZeroJet dimension (disk radius) field) |>.comp zeroLimit
    have zeroBase : jetBase dimension (disk radius) (.graph 0 0) (rawZeroJet dimension (disk radius) field) = field :=
      rawZeroJet_base dimension (disk radius) field
    have equality : (fun number => jetBase dimension (disk radius) (.graph 0 0)
        (restrictJet dimension radius (.graph 0 0)
          (stepJet dimension radius positiveRadius (.graph 0 0) (steps number) (rawZeroJet dimension (disk radius) field)))) =
        (fun number => Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))
          (stepField dimension radius positiveRadius (steps number) field)) := by
      funext number
      exact (restrict_stepJet_base dimension radius positiveRadius (.graph 0 0) (steps number)
        (rawZeroJet dimension (disk radius) field)).trans
        (congrArg (fun value => Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
          (Set.subset_univ (disk radius)) (stepField dimension radius positiveRadius (steps number) value)) zeroBase)
    change Tendsto (fun number => jetBase dimension (disk radius) (.graph 0 0)
      (restrictJet dimension radius (.graph 0 0)
        (stepJet dimension radius positiveRadius (.graph 0 0) (steps number) (rawZeroJet dimension (disk radius) field))))
      atTop (𝓝 (jetBase dimension (disk radius) (.graph 0 0) (rawZeroJet dimension (disk radius) field))) at limit
    rwa [equality, zeroBase] at limit
  refine ⟨steps, scaleLimit, epsilonLimit, fun number => (properties number).2.2.1,
    fun number => stepFunction_core dimension radius positiveRadius (steps number) field, rawLimit, ?_⟩
  intro index
  constructor
  · intro number
    have realized := stepJet_realizes dimension radius positiveRadius (grades index) (steps number) (jets index)
    rwa [sameBase index] at realized
  · exact limits index.succ

end Grad.SmoothDensity
