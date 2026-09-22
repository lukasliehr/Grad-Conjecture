import MP1Interface
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers

universe valueUniverse parameterUniverse

namespace Grad.Mollifier.Pointwise.Bridge

abbrev VolumeL2 (Value : Type valueUniverse) [NormedAddCommGroup Value] :=
  Lp Value 2 (volume : Measure Spatial)

def finiteSetIntegral (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (region : Set Spatial)
    (measurableRegion : MeasurableSet region) (finiteRegion : volume region ≠ ⊤) :
    VolumeL2 Value →L[ℂ] Value :=
  (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] Value →L[ℂ] Value).lpPairing volume 2 2
    (indicatorConstLp 2 measurableRegion finiteRegion (1 : ℂ))

def FiniteSetIntegralGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (region : Set Spatial) (measurableRegion : MeasurableSet region)
    (finiteRegion : volume region ≠ ⊤) (field : VolumeL2 Value),
    finiteSetIntegral Value region measurableRegion finiteRegion field =
      (∫ point in region, field point) ∧
    (∫ point in region, ‖field point‖) ≤ Real.sqrt (volume.real region) * ‖field‖

def LocalProductGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (parameterMeasure : Measure Parameter) [SigmaFinite parameterMeasure]
    (family : Parameter → VolumeL2 Value) (representative : Parameter → Spatial → Value),
    Integrable family parameterMeasure →
    AEStronglyMeasurable (Function.uncurry representative) (parameterMeasure.prod volume) →
    (∀ᵐ parameter ∂parameterMeasure, family parameter =ᵐ[volume] representative parameter) →
    ∀ region : Set Spatial, MeasurableSet region → volume region ≠ ⊤ →
      Integrable (Function.uncurry representative) (parameterMeasure.prod (volume.restrict region))

def LocalFubiniGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (parameterMeasure : Measure Parameter) [SigmaFinite parameterMeasure]
    (family : Parameter → VolumeL2 Value) (representative : Parameter → Spatial → Value),
    Integrable family parameterMeasure →
    AEStronglyMeasurable (Function.uncurry representative) (parameterMeasure.prod volume) →
    (∀ᵐ parameter ∂parameterMeasure, family parameter =ᵐ[volume] representative parameter) →
    ∀ region : Set Spatial, MeasurableSet region → volume region ≠ ⊤ →
      (∫ point in region, (∫ parameter, family parameter ∂parameterMeasure) point) =
        ∫ point in region, (∫ parameter, representative parameter point ∂parameterMeasure)

def LpIntegralRepresentativeGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (Parameter : Type parameterUniverse) [MeasurableSpace Parameter]
    (parameterMeasure : Measure Parameter) [SigmaFinite parameterMeasure]
    (family : Parameter → VolumeL2 Value) (representative : Parameter → Spatial → Value),
    Integrable family parameterMeasure →
    AEStronglyMeasurable (Function.uncurry representative) (parameterMeasure.prod volume) →
    (∀ᵐ parameter ∂parameterMeasure, family parameter =ᵐ[volume] representative parameter) →
    (∀ᵐ point ∂volume, Integrable (fun parameter => representative parameter point) parameterMeasure) ∧
    ((∫ parameter, family parameter ∂parameterMeasure) : VolumeL2 Value) =ᵐ[volume]
      (fun point => ∫ parameter, representative parameter point ∂parameterMeasure) ∧
    MemLp (fun point => ∫ parameter, representative parameter point ∂parameterMeasure) 2 volume

def TranslationSpecializationGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), Integrable kernel volume →
    ∀ field : DomainL2 Value Set.univ,
    Integrable (fun offset : Spatial =>
      kernel offset • Grad.SpatialTranslation.translation Value offset field) volume →
    (∀ offset : Spatial, Grad.SpatialTranslation.translation Value offset field =ᵐ[volume]
      (fun point => field (point - offset))) →
    Grad.SpatialTranslation.average Value kernel field =ᵐ[volume]
      smoothRepresentative Value kernel field ∧
    MemLp (smoothRepresentative Value kernel field) 2 volume

def BlockGoal : Prop :=
  FiniteSetIntegralGoal.{valueUniverse} ∧
    LocalProductGoal.{valueUniverse, parameterUniverse} ∧
    LocalFubiniGoal.{valueUniverse, parameterUniverse} ∧
    LpIntegralRepresentativeGoal.{valueUniverse, parameterUniverse} ∧
    TranslationSpecializationGoal.{valueUniverse}

end Grad.Mollifier.Pointwise.Bridge
