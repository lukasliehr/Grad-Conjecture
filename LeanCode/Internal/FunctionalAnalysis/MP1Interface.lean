import T1Interface
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open scoped BigOperators ContDiff

universe valueUniverse

namespace Grad.Mollifier.Pointwise

abbrev Word (rank : ℕ) := Fin rank → Fin 2

def orderedDerivative {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (word : Word rank) (function : Spatial → Value) : Spatial → Value :=
  fun point => iteratedFDeriv ℝ rank function point (fun position => spatialDirection (word position))

def convolution {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (kernel : Spatial → ℝ) (function : Spatial → Value) : Spatial → Value :=
  fun point => ∫ source : Spatial, kernel (point - source) • function source

def rawBump (point : Spatial) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace Spatial).toFun 2 ((2 : ℝ) • point)

def eta (point : Spatial) : ℝ := rawBump point / ∫ source : Spatial, rawBump source

def scaledEta (epsilon : ℝ) (point : Spatial) : ℝ :=
  (epsilon ^ 2)⁻¹ * eta (epsilon⁻¹ • point)

def smoothRepresentative (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (kernel : Spatial → ℝ) (field : DomainL2 Value Set.univ) :
    Spatial → Value := convolution kernel field

def derivativeField (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ)
    (rank : ℕ) (word : Word rank) (field : DomainL2 Value Set.univ) : DomainL2 Value Set.univ :=
  Grad.SpatialTranslation.average Value (orderedDerivative rank word kernel) field

def orderedFields (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ)
    (rank : ℕ) (field : DomainL2 Value Set.univ) : Tensor rank (DomainL2 Value Set.univ) :=
  tensorOfCoordinates rank (fun word => derivativeField Value kernel rank word field)

def LocalGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (field : DomainL2 Value Set.univ), LocallyIntegrable field volume

def KernelDerivativeGoal : Prop :=
  ∀ (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ (rank : ℕ) (word : Word rank),
      ContDiff ℝ ∞ (orderedDerivative rank word kernel) ∧
      HasCompactSupport (orderedDerivative rank word kernel) ∧
      tsupport (orderedDerivative rank word kernel) ⊆ tsupport kernel ∧
      Integrable (orderedDerivative rank word kernel) volume

def PointwiseGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ field : DomainL2 Value Set.univ,
      (∀ point : Spatial, Integrable (fun source : Spatial => kernel (point - source) • field source) volume) ∧
      ContDiff ℝ ∞ (smoothRepresentative Value kernel field) ∧
      (∀ (rank : ℕ) (word : Word rank) (point : Spatial),
        Integrable (fun source : Spatial => orderedDerivative rank word kernel (point - source) •
          field source) volume ∧
        orderedDerivative rank word (smoothRepresentative Value kernel field) point =
          ∫ source : Spatial, orderedDerivative rank word kernel (point - source) • field source)

def IndependenceGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ) (field : DomainL2 Value Set.univ)
    (representative : Spatial → Value), representative =ᵐ[volume] field →
      convolution kernel representative = smoothRepresentative Value kernel field

def BumpGoal : Prop :=
  (∀ point : Spatial, rawBump point = Real.smoothTransition (2 - 2 * ‖point‖)) ∧
    Integrable rawBump volume ∧ 0 < (∫ point : Spatial, rawBump point) ∧
    (∀ point : Spatial, 0 ≤ eta point) ∧ ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧
    Function.support eta = Metric.ball (0 : Spatial) 1 ∧
    tsupport eta = Metric.closedBall (0 : Spatial) 1 ∧
    Integrable eta volume ∧ (∫ point : Spatial, eta point) = 1 ∧
    (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial), eta (orthogonal point) = eta point)

def ScalingGoal : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    (∀ point : Spatial, scaledEta epsilon point = (epsilon ^ 2)⁻¹ * eta (epsilon⁻¹ • point)) ∧
    (∀ point : Spatial, 0 ≤ scaledEta epsilon point) ∧
    ContDiff ℝ ∞ (scaledEta epsilon) ∧ HasCompactSupport (scaledEta epsilon) ∧
    Function.support (scaledEta epsilon) = Metric.ball (0 : Spatial) epsilon ∧
    tsupport (scaledEta epsilon) = Metric.closedBall (0 : Spatial) epsilon ∧
    Integrable (scaledEta epsilon) volume ∧ (∫ point : Spatial, scaledEta epsilon point) = 1 ∧
    Grad.SpatialTranslation.kernelL1 (scaledEta epsilon) = 1 ∧
    (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (point : Spatial),
      scaledEta epsilon (orthogonal point) = scaledEta epsilon point)

def AverageRealizationGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ field : DomainL2 Value Set.univ,
      Grad.SpatialTranslation.average Value kernel field =ᵐ[volume] smoothRepresentative Value kernel field ∧
      MemLp (smoothRepresentative Value kernel field) 2 volume

def DerivativeL2Goal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∀ (field : DomainL2 Value Set.univ) (rank : ℕ) (word : Word rank),
      derivativeField Value kernel rank word field =ᵐ[volume]
        orderedDerivative rank word (smoothRepresentative Value kernel field) ∧
      MemLp (orderedDerivative rank word (smoothRepresentative Value kernel field)) 2 volume ∧
      ‖derivativeField Value kernel rank word field‖ ≤
        Grad.SpatialTranslation.kernelL1 (orderedDerivative rank word kernel) * ‖field‖

def OperatorGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), ContDiff ℝ ∞ kernel → HasCompactSupport kernel →
    ∃ operator : DomainL2 Value Set.univ →L[ℂ] DomainL2 Value Set.univ,
      (∀ field : DomainL2 Value Set.univ, operator field = Grad.SpatialTranslation.average Value kernel field) ∧
      ‖operator‖ ≤ Grad.SpatialTranslation.kernelL1 kernel

def MollifierSpecification (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (epsilon : ℝ)
    (operator : DomainL2 Value Set.univ →L[ℂ] DomainL2 Value Set.univ) : Prop :=
  (∀ field : DomainL2 Value Set.univ,
    operator field = Grad.SpatialTranslation.average Value (scaledEta epsilon) field) ∧
    ‖operator‖ ≤ 1 ∧
    (∀ field : DomainL2 Value Set.univ,
      ‖operator field‖ ≤ ‖field‖ ∧
      operator field =ᵐ[volume] smoothRepresentative Value (scaledEta epsilon) field ∧
      ContDiff ℝ ∞ (smoothRepresentative Value (scaledEta epsilon) field) ∧
      ∀ (rank : ℕ) (word : Word rank),
        derivativeField Value (scaledEta epsilon) rank word field =ᵐ[volume]
          orderedDerivative rank word (smoothRepresentative Value (scaledEta epsilon) field) ∧
        MemLp (orderedDerivative rank word (smoothRepresentative Value (scaledEta epsilon) field)) 2 volume ∧
        ‖derivativeField Value (scaledEta epsilon) rank word field‖ ≤
          Grad.SpatialTranslation.kernelL1 (orderedDerivative rank word (scaledEta epsilon)) * ‖field‖)

def MollifierGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (epsilon : ℝ), 0 < epsilon →
    ∃ operator : DomainL2 Value Set.univ →L[ℂ] DomainL2 Value Set.univ,
      MollifierSpecification Value epsilon operator

def HessianGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (epsilon : ℝ), 0 < epsilon →
    ∀ field : DomainL2 Value Set.univ,
      (∀ᵐ point ∂volume, ∀ word : Word 2,
        orderedFields Value (scaledEta epsilon) 2 field word point =
          iteratedFDeriv ℝ 2 (smoothRepresentative Value (scaledEta epsilon) field) point
            (fun position => spatialDirection (word position))) ∧
      ‖orderedFields Value (scaledEta epsilon) 2 field‖ ^ 2 ≤
        (∑ word : Word 2,
          Grad.SpatialTranslation.kernelL1 (orderedDerivative 2 word (scaledEta epsilon)) ^ 2) * ‖field‖ ^ 2

def CanonicalGoal : Prop :=
  ∀ (dimension : ℕ) (epsilon : ℝ), 0 < epsilon →
    ∃ operator : FieldL2 dimension Set.univ →L[ℂ] FieldL2 dimension Set.univ,
      MollifierSpecification (CellValues dimension) epsilon operator

def ZeroGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ) (field : DomainL2 Value Set.univ) (word : Word 0),
    derivativeField Value kernel 0 word field = Grad.SpatialTranslation.average Value kernel field ∧
      orderedDerivative 0 word (smoothRepresentative Value kernel field) = smoothRepresentative Value kernel field

def IndependentGoal : Prop :=
  LocalGoal.{valueUniverse} ∧ KernelDerivativeGoal ∧ PointwiseGoal.{valueUniverse} ∧
    IndependenceGoal.{valueUniverse} ∧ BumpGoal ∧ ScalingGoal

def DependentGoal : Prop :=
  AverageRealizationGoal.{valueUniverse} ∧ DerivativeL2Goal.{valueUniverse} ∧ OperatorGoal.{valueUniverse} ∧
    MollifierGoal.{valueUniverse} ∧ HessianGoal.{valueUniverse} ∧ CanonicalGoal ∧ ZeroGoal.{valueUniverse}

def BlockGoal : Prop := IndependentGoal.{valueUniverse} ∧ DependentGoal.{valueUniverse}

end Grad.Mollifier.Pointwise
