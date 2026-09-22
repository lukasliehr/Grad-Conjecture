import SD1Localized

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues FieldL2)
open Grad.SpatialDilation (disk)
open scoped ContDiff Topology

namespace Grad.SmoothDensity

theorem block_consumer : BlockGoal :=
  ⟨raw_zero_goal, radial_goal, higher_finite_goal, stage_goal, finite_choice_goal, density_goal, localized_goal⟩

theorem CT_CRT09 : DensityGoal ∧ LocalizedGoal := ⟨density_goal, localized_goal⟩

theorem graph_consumer (dimension count : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (orders weights : Fin count → ℕ) (field : FieldL2 dimension (disk radius))
    (jets : ∀ index, Grad.WeightedJets.GraphGrade dimension (orders index) (weights index) (disk radius))
    (sameBase : ∀ index, Grad.WeightedJets.base dimension (orders index) (disk radius) (fun _ => weights index)
      (jets index) = field) :
    DensityResult dimension count radius positiveRadius (fun index => .graph (orders index) (weights index)) field jets :=
  density_goal dimension count radius positiveRadius
    (fun index => .graph (orders index) (weights index)) field jets sameBase

theorem mixed_consumer (dimension count : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (orders : Fin count → ℕ) (field : FieldL2 dimension (disk radius))
    (jets : ∀ index, Grad.WeightedJets.Mixed dimension (orders index) (disk radius))
    (sameBase : ∀ index, Grad.WeightedJets.base dimension (orders index) (disk radius)
      (fun beta => orders index - Grad.WeightedJets.degree beta) (jets index) = field) :
    DensityResult dimension count radius positiveRadius (fun index => .mixed (orders index)) field jets :=
  density_goal dimension count radius positiveRadius (fun index => .mixed (orders index)) field jets sameBase

theorem empty_list_consumer (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (field : FieldL2 dimension (disk radius)) :
    DensityResult dimension 0 radius positiveRadius Fin.elim0 field (fun index => Fin.elim0 index) :=
  density_goal dimension 0 radius positiveRadius _ field _ (fun index => Fin.elim0 index)

theorem fixed_higher_finite (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) (power rank : ℕ) (word : Fin rank → Fin 2) :
    MemLp (weightedDerivative dimension power rank word (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)
      (stepFunction dimension radius positiveRadius step field)) 2 volume :=
  (higher_finite_goal dimension _ _ (stepFunction_core dimension radius positiveRadius step field) power rank word).2.2.1

end Grad.SmoothDensity
