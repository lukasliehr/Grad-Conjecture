import SD1Core

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.SpatialDilation (disk expandedDisk)
open scoped ContDiff Topology BigOperators

namespace Grad.SmoothDensity

set_option maxHeartbeats 1600000

theorem cutoffMultiplier_base (dimension : ℕ) (domain support : Set Spatial)
    (openDomain : IsOpen domain) (cutoff : Grad.CompactCutoff.Cutoff support domain)
    (grade : Grade) (jet : Jet dimension domain grade) :
    jetBase dimension domain grade
        (Grad.WeightedJets.SpatialMultiplier.compactJetMultiplier dimension grade.order domain openDomain
          cutoff.toFun cutoff.smooth cutoff.compact grade.exponent grade.antitone jet) =
      Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension domain openDomain
        (Grad.CompactCutoff.boundedScalar cutoff domain) (jetBase dimension domain grade jet) := by
  change Grad.WeightedJets.base dimension grade.order domain grade.exponent
    (Grad.WeightedJets.SpatialMultiplier.jetMultiplier dimension grade.order domain openDomain
      (Grad.WeightedJets.SpatialMultiplier.compactSymbol grade.order domain cutoff.toFun cutoff.smooth cutoff.compact)
      grade.exponent grade.antitone jet) = _
  rw [Grad.WeightedJets.SpatialMultiplier.jetMultiplier_base_apply]
  exact congrArg (fun mapping => mapping (jetBase dimension domain grade jet))
    (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier_congr dimension domain openDomain _ _ rfl)

theorem dilatedJet_base (dimension : ℕ) (radius : ℝ) (grade : Grade) (step : Step radius)
    (jet : Jet dimension (disk radius) grade) :
    jetBase dimension (expandedDisk radius step.scale) grade (dilatedJet dimension radius grade step jet) =
      Grad.SpatialDilation.rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet step.scale
        (jetBase dimension (disk radius) grade jet) :=
  Grad.SpatialDilation.jetDilation_base dimension grade.order radius step.scale grade.exponent jet

theorem extendedJet_base (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) (jet : Jet dimension (disk radius) grade) :
    jetBase dimension Set.univ grade (extendedJet dimension radius positiveRadius grade step jet) =
      preparedField dimension radius positiveRadius step (jetBase dimension (disk radius) grade jet) := by
  let cutoff := collar radius positiveRadius step.scale step.strict
  let domain := expandedDisk radius step.scale
  let openDomain := Grad.SpatialDilation.expandedDisk_open radius step.scale
  let symbol := Grad.WeightedJets.SpatialMultiplier.compactSymbol grade.order domain
    cutoff.toFun cutoff.smooth cutoff.compact
  let localizer := Grad.WeightedJets.ZeroExtension.compactLocalizer domain (tsupport cutoff.toFun)
    cutoff.compact openDomain (collar_supported radius positiveRadius step.scale step.strict)
  refine (Grad.WeightedJets.ZeroExtension.extendedMultiplier_base dimension grade.order domain openDomain
    symbol localizer grade.exponent grade.antitone (dilatedJet dimension radius grade step jet)).trans ?_
  apply congrArg (Grad.WeightedJets.ZeroExtension.fieldExtension (CellValues dimension)
    (expandedDisk radius step.scale) (Grad.SpatialDilation.expandedDisk_open radius step.scale).measurableSet)
  refine (congrArg (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension domain openDomain
    (Grad.WeightedJets.SpatialMultiplier.derivativeScalar symbol (Grad.WeightedJets.zeroIndex grade.order)))
    (dilatedJet_base dimension radius grade step jet)).trans ?_
  exact congrArg (fun mapping => mapping
    (Grad.SpatialDilation.rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet step.scale
      (jetBase dimension (disk radius) grade jet)))
    (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier_congr dimension _
      (Grad.SpatialDilation.expandedDisk_open radius step.scale) _ _ rfl)

theorem regularizedJet_base (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) (jet : Jet dimension (disk radius) grade) :
    jetBase dimension Set.univ grade (regularizedJet dimension radius positiveRadius grade step jet) =
      Grad.SpatialTranslation.average (CellValues dimension) (Grad.Mollifier.Pointwise.scaledEta step.epsilon)
        (preparedField dimension radius positiveRadius step (jetBase dimension (disk radius) grade jet)) := by
  exact (Grad.Mollifier.WeakJets.Consumer.weightedBase dimension grade.order grade.exponent step.epsilon
    step.positiveEpsilon (extendedJet dimension radius positiveRadius grade step jet)).trans
    (congrArg (Grad.SpatialTranslation.average (CellValues dimension) (Grad.Mollifier.Pointwise.scaledEta step.epsilon))
      (extendedJet_base dimension radius positiveRadius grade step jet))

theorem stepJet_base (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) (jet : Jet dimension (disk radius) grade) :
    jetBase dimension Set.univ grade (stepJet dimension radius positiveRadius grade step jet) =
      stepField dimension radius positiveRadius step (jetBase dimension (disk radius) grade jet) := by
  exact (Grad.WeightedJets.CellCutoff.cutoff_base dimension grade.order Set.univ grade.exponent
    (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)
    (regularizedJet dimension radius positiveRadius grade step jet)).trans
    (congrArg (Grad.WeightedJets.CellCutoff.fieldCutoff dimension Set.univ
      (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius))
      (regularizedJet_base dimension radius positiveRadius grade step jet))

theorem preparedField_supported (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) :
    Grad.Mollifier.Locality.FieldSupported (CellValues dimension)
      (tsupport (collar radius positiveRadius step.scale step.strict).toFun)
      (preparedField dimension radius positiveRadius step field) := by
  let domain := expandedDisk radius step.scale
  let openDomain := Grad.SpatialDilation.expandedDisk_open radius step.scale
  let scalar := Grad.CompactCutoff.boundedScalar (collar radius positiveRadius step.scale step.strict) domain
  let dilated := Grad.SpatialDilation.rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet step.scale field
  let multiplied := Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension domain openDomain scalar dilated
  have multiplication := (ae_restrict_iff' openDomain.measurableSet).mp
    (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier_ae dimension domain openDomain scalar dilated)
  have extension := Grad.WeightedJets.ZeroExtension.fieldExtension_ae
    (CellValues dimension) domain openDomain.measurableSet multiplied
  filter_upwards [multiplication, extension] with point multipliedAt extendedAt
  intro outside
  change Grad.WeightedJets.ZeroExtension.fieldExtension (CellValues dimension) domain openDomain.measurableSet
    multiplied point = 0
  rw [extendedAt]
  by_cases inside : point ∈ domain
  · rw [Set.indicator_of_mem inside]
    apply lp.ext
    funext cell
    change multiplied point cell = 0
    rw [multipliedAt inside cell]
    have scalarZero : scalar.toFun point = 0 := image_eq_zero_of_notMem_tsupport outside
    rw [scalarZero, Complex.ofReal_zero, zero_smul]
  · rw [Set.indicator_of_notMem inside]

theorem stepFunction_core (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) :
    CoreLaws dimension (stepFunction dimension radius positiveRadius step field)
      (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius) := by
  have convolution := Grad.Mollifier.Locality.Consumer.smoothCompactField dimension step.epsilon step.positiveEpsilon
    (tsupport (collar radius positiveRadius step.scale step.strict).toFun)
    (collar radius positiveRadius step.scale step.strict).compact
    (preparedField dimension radius positiveRadius step field)
    (preparedField_supported dimension radius positiveRadius step field)
  let projection := Grad.CellProjections.Generic.projection (PhysicalValue dimension)
    (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)
  refine ⟨(projection.contDiff.restrict_scalars ℝ).comp convolution.1,
    convolution.2.1.2.2.comp_left projection.map_zero, ?_⟩
  intro point cell outside
  exact (Grad.CellProjections.Generic.projection_coordinate (PhysicalValue dimension) _ _ cell).trans
    (if_neg outside)

theorem stepField_ae (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) :
    stepField dimension radius positiveRadius step field =ᵐ[volume]
      stepFunction dimension radius positiveRadius step field := by
  have average := (Grad.Mollifier.WeakJets.average_realization (CellValues dimension)
    (Grad.Mollifier.Pointwise.scaledEta step.epsilon)
    (Grad.Mollifier.Pointwise.scaledEta_integrable step.epsilon step.positiveEpsilon)
    (preparedField dimension radius positiveRadius step field)).1
  have projected := Grad.CellProjections.Generic.field_projection_coordinate (PhysicalValue dimension)
    (volume.restrict Set.univ) (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)
    (Grad.SpatialTranslation.average (CellValues dimension) (Grad.Mollifier.Pointwise.scaledEta step.epsilon)
      (preparedField dimension radius positiveRadius step field))
  have projectedVolume := Grad.SpatialTranslation.ae_univ_iff.mp projected
  filter_upwards [average, projectedVolume] with point averagedAt projectedAt
  apply lp.ext
  funext cell
  change Grad.CellProjections.Generic.fieldProjection _ _ _ _ point cell = _
  rw [projectedAt cell, averagedAt, stepFunction,
    Grad.CellProjections.Generic.projection_coordinate]

end Grad.SmoothDensity
