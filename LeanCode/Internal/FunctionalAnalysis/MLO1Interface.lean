import MP1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.Mollifier.Pointwise
open scoped ContDiff Pointwise

universe valueUniverse

namespace Grad.Mollifier.Locality

def thickening (carrier : Set Spatial) (epsilon : ℝ) : Set Spatial :=
  carrier + Metric.closedBall (0 : Spatial) epsilon

def safeRegion (domain : Set Spatial) (epsilon : ℝ) : Set Spatial :=
  {point | Metric.closedBall point epsilon ⊆ domain}

def KernelSupported (kernel : Spatial → ℝ) (epsilon : ℝ) : Prop :=
  tsupport kernel ⊆ Metric.closedBall (0 : Spatial) epsilon

def FieldSupported (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (carrier : Set Spatial) (field : DomainL2 Value Set.univ) : Prop :=
  ∀ᵐ point ∂volume, point ∉ carrier → field point = 0

def FieldsAgree (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (domain : Set Spatial)
    (first second : DomainL2 Value Set.univ) : Prop :=
  first =ᵐ[volume.restrict domain] second

def SupportResult {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (function : Spatial → Value) (carrier : Set Spatial) : Prop :=
  (∀ point : Spatial, point ∉ carrier → function point = 0) ∧
    tsupport function ⊆ carrier ∧ HasCompactSupport function

def SupportSpecification (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (carrier : Set Spatial) (epsilon : ℝ)
    (kernel : Spatial → ℝ) (field : DomainL2 Value Set.univ) : Prop :=
  SupportResult (smoothRepresentative Value kernel field) (thickening carrier epsilon) ∧
    ∀ (rank : ℕ) (word : Word rank),
      SupportResult (smoothRepresentative Value (orderedDerivative rank word kernel) field)
        (thickening carrier epsilon) ∧
      SupportResult (orderedDerivative rank word (smoothRepresentative Value kernel field))
        (thickening carrier epsilon) ∧
      orderedDerivative rank word (smoothRepresentative Value kernel field) =
        smoothRepresentative Value (orderedDerivative rank word kernel) field

def AgreementAt (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (kernel : Spatial → ℝ)
    (first second : DomainL2 Value Set.univ) (point : Spatial) : Prop :=
  smoothRepresentative Value kernel first point = smoothRepresentative Value kernel second point ∧
    ∀ (rank : ℕ) (word : Word rank),
      orderedDerivative rank word (smoothRepresentative Value kernel first) point =
        orderedDerivative rank word (smoothRepresentative Value kernel second) point ∧
      smoothRepresentative Value (orderedDerivative rank word kernel) first point =
        smoothRepresentative Value (orderedDerivative rank word kernel) second point

def AgreementSpecification (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (domain : Set Spatial) (epsilon : ℝ)
    (kernel : Spatial → ℝ) (first second : DomainL2 Value Set.univ) : Prop :=
  ∀ point ∈ safeRegion domain epsilon, AgreementAt Value kernel first second point

def KernelSupportGoal : Prop :=
  ∀ (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ epsilon : ℝ, KernelSupported kernel epsilon → ∀ (rank : ℕ) (word : Word rank),
      ContDiff ℝ ∞ (orderedDerivative rank word kernel) ∧
      HasCompactSupport (orderedDerivative rank word kernel) ∧
      KernelSupported (orderedDerivative rank word kernel) epsilon

def SupportGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ epsilon : ℝ, KernelSupported kernel epsilon → ∀ carrier : Set Spatial, IsCompact carrier →
      ∀ field : DomainL2 Value Set.univ, FieldSupported Value carrier field →
        SupportSpecification Value carrier epsilon kernel field

def AgreementGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ epsilon : ℝ, KernelSupported kernel epsilon → ∀ domain : Set Spatial, IsOpen domain →
      ∀ first second : DomainL2 Value Set.univ, FieldsAgree Value domain first second →
        AgreementSpecification Value domain epsilon kernel first second

def ScaledSpecification (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (epsilon : ℝ) : Prop :=
  (∀ carrier : Set Spatial, IsCompact carrier → ∀ field : DomainL2 Value Set.univ,
    FieldSupported Value carrier field → SupportSpecification Value carrier epsilon (scaledEta epsilon) field) ∧
  (∀ domain : Set Spatial, IsOpen domain → ∀ first second : DomainL2 Value Set.univ,
    FieldsAgree Value domain first second →
      AgreementSpecification Value domain epsilon (scaledEta epsilon) first second)

def ScaledGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (epsilon : ℝ), 0 < epsilon → ScaledSpecification Value epsilon

def DiskSpecification (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (center : Spatial) (innerRadius outerRadius epsilon : ℝ)
    (kernel : Spatial → ℝ) : Prop :=
  thickening (Metric.closedBall center innerRadius) epsilon ⊆ Metric.ball center outerRadius ∧
    Metric.closedBall center innerRadius ⊆ safeRegion (Metric.ball center outerRadius) epsilon ∧
    (∀ field : DomainL2 Value Set.univ,
      FieldSupported Value (Metric.closedBall center innerRadius) field →
        SupportResult (smoothRepresentative Value kernel field) (Metric.ball center outerRadius) ∧
        ∀ (rank : ℕ) (word : Word rank),
          SupportResult (orderedDerivative rank word (smoothRepresentative Value kernel field))
            (Metric.ball center outerRadius) ∧
          SupportResult (smoothRepresentative Value (orderedDerivative rank word kernel) field)
            (Metric.ball center outerRadius)) ∧
    (∀ first second : DomainL2 Value Set.univ, FieldsAgree Value (Metric.ball center outerRadius) first second →
      ∀ point ∈ Metric.closedBall center innerRadius, AgreementAt Value kernel first second point)

def DiskGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ epsilon : ℝ, 0 ≤ epsilon → KernelSupported kernel epsilon →
      ∀ (center : Spatial) (innerRadius outerRadius : ℝ), 0 ≤ innerRadius →
        innerRadius + epsilon < outerRadius → DiskSpecification Value center innerRadius outerRadius epsilon kernel

def CanonicalGoal : Prop :=
  ∀ (dimension : ℕ) (epsilon : ℝ), 0 < epsilon →
    ScaledSpecification (CellValues dimension) epsilon ∧
      ∀ (center : Spatial) (innerRadius outerRadius : ℝ), 0 ≤ innerRadius →
        innerRadius + epsilon < outerRadius →
          DiskSpecification (CellValues dimension) center innerRadius outerRadius epsilon (scaledEta epsilon)

def CoordinateGoal : Prop :=
  ∀ (dimension : ℕ) (epsilon : ℝ), 0 < epsilon → ∀ domain : Set Spatial, IsOpen domain →
    ∀ first second : FieldL2 dimension Set.univ, FieldsAgree (CellValues dimension) domain first second →
      ∀ point ∈ safeRegion domain epsilon, ∀ (cell : ℤ) (physical : Fin dimension),
        smoothRepresentative (CellValues dimension) (scaledEta epsilon) first point cell physical =
          smoothRepresentative (CellValues dimension) (scaledEta epsilon) second point cell physical ∧
        ∀ (rank : ℕ) (word : Word rank),
          orderedDerivative rank word (smoothRepresentative (CellValues dimension) (scaledEta epsilon) first)
            point cell physical =
          orderedDerivative rank word (smoothRepresentative (CellValues dimension) (scaledEta epsilon) second)
            point cell physical

def ZeroGoal : Prop :=
  (∀ epsilon : ℝ, 0 < epsilon → ScaledSpecification (CellValues 0) epsilon) ∧
    ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
      [CompleteSpace Value] (kernel : Spatial → ℝ) (field : DomainL2 Value Set.univ) (word : Word 0),
      orderedDerivative 0 word (smoothRepresentative Value kernel field) = smoothRepresentative Value kernel field

def BlockGoal : Prop :=
  KernelSupportGoal ∧ SupportGoal.{valueUniverse} ∧ AgreementGoal.{valueUniverse} ∧
    ScaledGoal.{valueUniverse} ∧ DiskGoal.{valueUniverse} ∧ CanonicalGoal ∧ CoordinateGoal ∧ ZeroGoal.{valueUniverse}

end Grad.Mollifier.Locality
