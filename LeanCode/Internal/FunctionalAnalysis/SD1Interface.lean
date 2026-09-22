import DIL1Consumer
import ZE1Compact
import JCCoherence
import WM1Consumers
import MLO1Consumers
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets (WJet JetIndex degree derivativeWord base)
open Grad.SpatialDilation (Scale disk expandedDisk diskMargin)
open scoped ContDiff Topology BigOperators

namespace Grad.SmoothDensity

inductive Grade where
  | graph (order weight : ℕ)
  | mixed (order : ℕ)

def Grade.order : Grade → ℕ
  | .graph order _ => order
  | .mixed order => order

def Grade.exponent : (grade : Grade) → JetIndex grade.order → ℕ
  | .graph _ weight => fun _ => weight
  | .mixed order => fun index => order - degree index

theorem Grade.antitone (grade : Grade) :
    Grad.WeightedJets.SpatialMultiplier.ExponentAntitone grade.exponent := by
  cases grade with
  | graph order weight =>
    exact Grad.WeightedJets.SpatialMultiplier.constantExponent_antitone order weight
  | mixed order => exact Grad.WeightedJets.SpatialMultiplier.mixedExponent_antitone order

abbrev Jet (dimension : ℕ) (domain : Set Spatial) (grade : Grade) :=
  WJet dimension grade.order domain grade.exponent

def jetBase (dimension : ℕ) (domain : Set Spatial) (grade : Grade) :
    Jet dimension domain grade →L[ℂ] FieldL2 dimension domain :=
  base dimension grade.order domain grade.exponent

def collar (radius : ℝ) (positiveRadius : 0 < radius) (scale : Scale) (strict : scale.val < 1) :=
  Grad.CompactCutoff.diskCutoff radius (diskMargin radius scale) positiveRadius.le
    ((Grad.SpatialDilation.geometry_goal.2 radius scale positiveRadius strict).1)

theorem collar_supported (radius : ℝ) (positiveRadius : 0 < radius)
    (scale : Scale) (strict : scale.val < 1) :
    tsupport (collar radius positiveRadius scale strict).toFun ⊆ expandedDisk radius scale := by
  rw [Grad.SpatialDilation.expandedDisk_eq,
    ← (Grad.SpatialDilation.geometry_goal.2 radius scale positiveRadius strict).2.1]
  exact (collar radius positiveRadius scale strict).supported

structure Step (radius : ℝ) where
  scale : Scale
  strict : scale.val < 1
  epsilon : ℝ
  positiveEpsilon : 0 < epsilon
  smallEpsilon : epsilon < diskMargin radius scale / 2
  cellRadius : ℕ

def dilatedJet (dimension : ℕ) (radius : ℝ) (grade : Grade) (step : Step radius) :=
  Grad.SpatialDilation.jetDilation dimension grade.order radius step.scale grade.exponent

def extendedJet (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) :
    Jet dimension (disk radius) grade →L[ℂ] Jet dimension Set.univ grade :=
  (Grad.WeightedJets.ZeroExtension.compactScalarExtension dimension grade.order
    (expandedDisk radius step.scale) (Grad.SpatialDilation.expandedDisk_open radius step.scale)
    (collar radius positiveRadius step.scale step.strict).toFun
    (collar radius positiveRadius step.scale step.strict).smooth
    (collar radius positiveRadius step.scale step.strict).compact
    (collar_supported radius positiveRadius step.scale step.strict) grade.exponent grade.antitone).comp
      (dilatedJet dimension radius grade step)

def regularizedJet (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) :
    Jet dimension (disk radius) grade →L[ℂ] Jet dimension Set.univ grade :=
  (Grad.Mollifier.WeakJets.Consumer.weightedRegularizer dimension grade.order grade.exponent step.epsilon).comp
    (extendedJet dimension radius positiveRadius grade step)

def stepJet (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grade : Grade) (step : Step radius) :
    Jet dimension (disk radius) grade →L[ℂ] Jet dimension Set.univ grade :=
  (Grad.WeightedJets.CellCutoff.cutoff dimension grade.order Set.univ grade.exponent
    (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)).comp
      (regularizedJet dimension radius positiveRadius grade step)

def restrictJet (dimension : ℕ) (radius : ℝ) (grade : Grade) :
    Jet dimension Set.univ grade →L[ℂ] Jet dimension (disk radius) grade :=
  Grad.WeightedJets.Restriction.restriction dimension grade.order (Set.subset_univ (disk radius))
    MeasurableSet.univ grade.exponent

def preparedField (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) : FieldL2 dimension Set.univ :=
  Grad.WeightedJets.ZeroExtension.fieldExtension (CellValues dimension) (expandedDisk radius step.scale)
    (Grad.SpatialDilation.expandedDisk_open radius step.scale).measurableSet
    (Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension (expandedDisk radius step.scale)
      (Grad.SpatialDilation.expandedDisk_open radius step.scale)
      (Grad.CompactCutoff.boundedScalar (collar radius positiveRadius step.scale step.strict)
        (expandedDisk radius step.scale))
      (Grad.SpatialDilation.rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet step.scale field))

def stepField (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) : FieldL2 dimension Set.univ :=
  Grad.WeightedJets.CellCutoff.fieldCutoff dimension Set.univ
    (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)
    (Grad.SpatialTranslation.average (CellValues dimension) (Grad.Mollifier.Pointwise.scaledEta step.epsilon)
      (preparedField dimension radius positiveRadius step field))

def stepFunction (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)) : Spatial → CellValues dimension :=
  fun point => Grad.CellProjections.Generic.projection (PhysicalValue dimension)
    (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)
    (Grad.Mollifier.Pointwise.smoothRepresentative (CellValues dimension)
      (Grad.Mollifier.Pointwise.scaledEta step.epsilon)
      (preparedField dimension radius positiveRadius step field) point)

def CoreLaws (dimension : ℕ) (function : Spatial → CellValues dimension) (cells : Finset ℤ) : Prop :=
  ContDiff ℝ ∞ function ∧ HasCompactSupport function ∧
    ∀ (point : Spatial) (cell : ℤ), cell ∉ cells → function point cell = 0

def Realizes (dimension : ℕ) (domain : Set Spatial) (grade : Grade)
    (function : Spatial → CellValues dimension) (jet : Jet dimension domain grade) : Prop :=
  jetBase dimension domain grade jet =ᵐ[volume.restrict domain] function ∧
    ∀ᵐ point ∂volume.restrict domain, ∀ (index : JetIndex grade.order) (cell : ℤ),
      jet.val index point cell = Grad.CellWeights.positiveFactor (grade.exponent index) cell •
        Grad.Mollifier.Pointwise.orderedDerivative (degree index) (derivativeWord index) function point cell

def weightedDerivative (dimension power rank : ℕ) (word : Fin rank → Fin 2)
    (cells : Finset ℤ) (function : Spatial → CellValues dimension) : Spatial → CellValues dimension :=
  fun point => ∑ cell ∈ cells, Grad.CellWeights.positiveFactor power cell •
    lp.single 2 cell (Grad.Mollifier.Pointwise.orderedDerivative rank word function point cell)

def HigherFiniteGoal : Prop :=
  ∀ (dimension : ℕ) (function : Spatial → CellValues dimension) (cells : Finset ℤ),
    CoreLaws dimension function cells → ∀ (power rank : ℕ) (word : Fin rank → Fin 2),
      ContDiff ℝ ∞ (weightedDerivative dimension power rank word cells function) ∧
      HasCompactSupport (weightedDerivative dimension power rank word cells function) ∧
      MemLp (weightedDerivative dimension power rank word cells function) 2 volume ∧
      ∀ (point : Spatial) (cell : ℤ),
        weightedDerivative dimension power rank word cells function point cell =
          Grad.CellWeights.positiveFactor power cell •
            Grad.Mollifier.Pointwise.orderedDerivative rank word function point cell

def StageGoal : Prop :=
  ∀ (dimension : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (step : Step radius) (field : FieldL2 dimension (disk radius)),
    CoreLaws dimension (stepFunction dimension radius positiveRadius step field)
      (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius) ∧
    (stepField dimension radius positiveRadius step field =ᵐ[volume]
      stepFunction dimension radius positiveRadius step field) ∧
    ∀ (grade : Grade) (jet : Jet dimension (disk radius) grade),
      jetBase dimension (disk radius) grade jet = field →
      jetBase dimension (expandedDisk radius step.scale) grade (dilatedJet dimension radius grade step jet) =
        Grad.SpatialDilation.rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet step.scale field ∧
      jetBase dimension Set.univ grade (extendedJet dimension radius positiveRadius grade step jet) =
        preparedField dimension radius positiveRadius step field ∧
      jetBase dimension Set.univ grade (regularizedJet dimension radius positiveRadius grade step jet) =
        Grad.SpatialTranslation.average (CellValues dimension) (Grad.Mollifier.Pointwise.scaledEta step.epsilon)
          (preparedField dimension radius positiveRadius step field) ∧
      jetBase dimension Set.univ grade (stepJet dimension radius positiveRadius grade step jet) =
        stepField dimension radius positiveRadius step field ∧
      Realizes dimension Set.univ grade (stepFunction dimension radius positiveRadius step field)
        (stepJet dimension radius positiveRadius grade step jet) ∧
      Realizes dimension (disk radius) grade (stepFunction dimension radius positiveRadius step field)
        (restrictJet dimension radius grade (stepJet dimension radius positiveRadius grade step jet)) ∧
      ‖stepJet dimension radius positiveRadius grade step jet‖ ^ 2 =
        ∑ index : JetIndex grade.order,
          (eLpNorm (weightedDerivative dimension (grade.exponent index) (degree index) (derivativeWord index)
            (Grad.WeightedJets.CellCutoff.centeredCells step.cellRadius)
            (stepFunction dimension radius positiveRadius step field)) 2 volume).toReal ^ 2 ∧
      ∀ (index : JetIndex grade.order) (cell : ℤ) (vector : PhysicalValue dimension)
        (test : Grad.WeightedJets.TestFunction (disk radius)),
        (∫ point in disk radius, test.toFun point • inner ℂ vector
          (Grad.Mollifier.Pointwise.orderedDerivative (degree index) (derivativeWord index)
            (stepFunction dimension radius positiveRadius step field) point cell)) =
          (-1 : ℂ) ^ degree index * ∫ point in disk radius,
            Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
              inner ℂ vector (stepFunction dimension radius positiveRadius step field point cell)

def RawZeroGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain),
    ∃ jet : Grad.WeightedJets.GraphGrade dimension 0 0 domain,
      base dimension 0 domain (fun _ => 0) jet = field ∧ ‖jet‖ = ‖field‖

def CommonBase (dimension count : ℕ) (radius : ℝ) (grades : Fin count → Grade)
    (field : FieldL2 dimension (disk radius)) (jets : ∀ index, Jet dimension (disk radius) (grades index)) : Prop :=
  ∀ index, jetBase dimension (disk radius) (grades index) (jets index) = field

def DensityResult (dimension count : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grades : Fin count → Grade) (field : FieldL2 dimension (disk radius))
    (jets : ∀ index, Jet dimension (disk radius) (grades index)) : Prop :=
  ∃ steps : ℕ → Step radius,
    Filter.Tendsto (fun number => (steps number).scale) Filter.atTop (𝓝 Grad.SpatialDilation.oneScale) ∧
    Filter.Tendsto (fun number => (steps number).epsilon) Filter.atTop (𝓝[>] (0 : ℝ)) ∧
    (∀ number, number ≤ (steps number).cellRadius) ∧
    (∀ number, CoreLaws dimension (stepFunction dimension radius positiveRadius (steps number) field)
      (Grad.WeightedJets.CellCutoff.centeredCells (steps number).cellRadius)) ∧
    Filter.Tendsto (fun number =>
      Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))
        (stepField dimension radius positiveRadius (steps number) field)) Filter.atTop (𝓝 field) ∧
    ∀ index,
      (∀ number, Realizes dimension Set.univ (grades index)
        (stepFunction dimension radius positiveRadius (steps number) field)
        (stepJet dimension radius positiveRadius (grades index) (steps number) (jets index))) ∧
      Filter.Tendsto (fun number => restrictJet dimension radius (grades index)
        (stepJet dimension radius positiveRadius (grades index) (steps number) (jets index)))
          Filter.atTop (𝓝 (jets index))

def FiniteChoiceGoal : Prop :=
  ∀ (dimension count : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grades : Fin count → Grade) (jets : ∀ index, Jet dimension (disk radius) (grades index))
    (scale : Scale) (_strict : scale.val < 1) (tolerance : ℝ), 0 < tolerance →
    ∀ minimumCells : ℕ, ∃ step : Step radius,
      step.scale = scale ∧ step.epsilon < tolerance ∧ minimumCells ≤ step.cellRadius ∧
      ∀ index,
        ‖regularizedJet dimension radius positiveRadius (grades index) step (jets index) -
          extendedJet dimension radius positiveRadius (grades index) step (jets index)‖ < tolerance ∧
        ‖stepJet dimension radius positiveRadius (grades index) step (jets index) -
          regularizedJet dimension radius positiveRadius (grades index) step (jets index)‖ < tolerance

def DensityGoal : Prop :=
  ∀ (dimension count : ℕ) (radius : ℝ) (positiveRadius : 0 < radius)
    (grades : Fin count → Grade) (field : FieldL2 dimension (disk radius))
    (jets : ∀ index, Jet dimension (disk radius) (grades index)),
    CommonBase dimension count radius grades field jets →
      DensityResult dimension count radius positiveRadius grades field jets

def plateauRadius (innerRadius outerRadius : ℝ) := innerRadius + (outerRadius - innerRadius) / 3

def supportRadius (innerRadius outerRadius : ℝ) := innerRadius + 2 * (outerRadius - innerRadius) / 3

def radialFunction (innerRadius outerRadius : ℝ) : Spatial → ℝ :=
  fun point => Real.smoothTransition
    ((supportRadius innerRadius outerRadius ^ 2 - ‖point‖ ^ 2) /
      (supportRadius innerRadius outerRadius ^ 2 - plateauRadius innerRadius outerRadius ^ 2))

def RadialLaws (innerRadius outerRadius : ℝ)
    (cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius)) : Prop :=
  cutoff.toFun = radialFunction innerRadius outerRadius ∧
    Set.EqOn cutoff.toFun (fun _ => 1) (Metric.closedBall (0 : Spatial) (plateauRadius innerRadius outerRadius)) ∧
    tsupport cutoff.toFun ⊆ Metric.closedBall (0 : Spatial) (supportRadius innerRadius outerRadius) ∧
    (∀ point ∈ Metric.closedBall (0 : Spatial) innerRadius, cutoff.toFun =ᶠ[𝓝 point] (fun _ => 1)) ∧
    (∀ (isometry : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial), cutoff.toFun (isometry point) = cutoff.toFun point) ∧
    ∀ (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial),
      |Grad.WeakTesting.orderedTestDerivative rank word cutoff.toFun point| ≤
        Grad.CompactCutoff.orderedBound cutoff word

def RadialGoal : Prop :=
  ∀ (innerRadius outerRadius : ℝ), 0 ≤ innerRadius → innerRadius < outerRadius →
    ∃ cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius),
      RadialLaws innerRadius outerRadius cutoff

def localizedJet (dimension : ℕ) (innerRadius outerRadius : ℝ) (grade : Grade)
    (cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius)) :
    Jet dimension (disk outerRadius) grade →L[ℂ] Jet dimension (disk outerRadius) grade :=
  Grad.WeightedJets.SpatialMultiplier.compactJetMultiplier dimension grade.order (disk outerRadius)
    Metric.isOpen_ball cutoff.toFun cutoff.smooth cutoff.compact grade.exponent grade.antitone

def localizedField (dimension : ℕ) (innerRadius outerRadius : ℝ)
    (cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius)) :=
  Grad.WeightedJets.SpatialMultiplier.fieldMultiplier dimension (disk outerRadius) Metric.isOpen_ball
    (Grad.CompactCutoff.boundedScalar cutoff (disk outerRadius))

def innerRestriction (dimension : ℕ) (innerRadius outerRadius : ℝ)
    (included : innerRadius ≤ outerRadius) (grade : Grade) :
    Jet dimension (disk outerRadius) grade →L[ℂ] Jet dimension (disk innerRadius) grade :=
  Grad.WeightedJets.Restriction.restriction dimension grade.order
    (Metric.ball_subset_ball included) Metric.isOpen_ball.measurableSet grade.exponent

def LocalizedGoal : Prop :=
  ∀ (dimension count : ℕ) (innerRadius outerRadius : ℝ) (nonnegativeInner : 0 ≤ innerRadius)
    (strictRadii : innerRadius < outerRadius) (grades : Fin count → Grade)
    (field : FieldL2 dimension (disk outerRadius)) (jets : ∀ index, Jet dimension (disk outerRadius) (grades index)),
    CommonBase dimension count outerRadius grades field jets →
    ∃ cutoff : Grad.CompactCutoff.Cutoff (Metric.closedBall (0 : Spatial) innerRadius) (disk outerRadius),
      RadialLaws innerRadius outerRadius cutoff ∧
      CommonBase dimension count outerRadius grades
        (localizedField dimension innerRadius outerRadius cutoff field)
        (fun index => localizedJet dimension innerRadius outerRadius (grades index) cutoff (jets index)) ∧
      (∀ index, innerRestriction dimension innerRadius outerRadius strictRadii.le (grades index)
          (localizedJet dimension innerRadius outerRadius (grades index) cutoff (jets index)) =
        innerRestriction dimension innerRadius outerRadius strictRadii.le (grades index) (jets index)) ∧
      ∃ steps : ℕ → Step outerRadius,
        Filter.Tendsto (fun number => (steps number).scale) Filter.atTop (𝓝 Grad.SpatialDilation.oneScale) ∧
        Filter.Tendsto (fun number => (steps number).epsilon) Filter.atTop (𝓝[>] (0 : ℝ)) ∧
        (∀ number, number ≤ (steps number).cellRadius) ∧
        (∀ number, CoreLaws dimension
          (stepFunction dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number)
            (localizedField dimension innerRadius outerRadius cutoff field))
          (Grad.WeightedJets.CellCutoff.centeredCells (steps number).cellRadius)) ∧
        (∀ number index, Realizes dimension Set.univ (grades index)
          (stepFunction dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number)
            (localizedField dimension innerRadius outerRadius cutoff field))
          (stepJet dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (grades index) (steps number)
            (localizedJet dimension innerRadius outerRadius (grades index) cutoff (jets index)))) ∧
        Filter.Tendsto (fun number =>
          Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk outerRadius))
            (stepField dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number)
              (localizedField dimension innerRadius outerRadius cutoff field)))
          Filter.atTop (𝓝 (localizedField dimension innerRadius outerRadius cutoff field)) ∧
        Filter.Tendsto (fun number =>
          Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk innerRadius))
            (stepField dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (steps number)
              (localizedField dimension innerRadius outerRadius cutoff field)))
          Filter.atTop (𝓝 (Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension)
            (show disk innerRadius ⊆ disk outerRadius from Metric.ball_subset_ball strictRadii.le) field)) ∧
        ∀ index,
          Filter.Tendsto (fun number => restrictJet dimension outerRadius (grades index)
            (stepJet dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (grades index) (steps number)
              (localizedJet dimension innerRadius outerRadius (grades index) cutoff (jets index))))
            Filter.atTop (𝓝 (localizedJet dimension innerRadius outerRadius (grades index) cutoff (jets index))) ∧
          Filter.Tendsto (fun number => innerRestriction dimension innerRadius outerRadius strictRadii.le (grades index)
            (restrictJet dimension outerRadius (grades index)
              (stepJet dimension outerRadius (nonnegativeInner.trans_lt strictRadii) (grades index) (steps number)
                (localizedJet dimension innerRadius outerRadius (grades index) cutoff (jets index)))))
            Filter.atTop (𝓝 (innerRestriction dimension innerRadius outerRadius strictRadii.le (grades index) (jets index)))

def BlockGoal : Prop :=
  RawZeroGoal ∧ RadialGoal ∧ HigherFiniteGoal ∧ StageGoal ∧ FiniteChoiceGoal ∧ DensityGoal ∧ LocalizedGoal

end Grad.SmoothDensity
