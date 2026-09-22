import GC1Proof
import WT1Proof
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (DomainL2 CellValues PhysicalValue FieldL2)
open scoped Topology ContDiff

universe valueUniverse otherUniverse

namespace Grad.SpatialTranslation

abbrev PlaneL2 (Value : Type valueUniverse) [NormedAddCommGroup Value] :=
  DomainL2 Value Set.univ

def shiftFamily : C(Spatial, C(Spatial, Spatial)) :=
  (ContinuousMap.mk (fun pair : Spatial × Spatial => pair.2 - pair.1)
    (continuous_snd.sub continuous_fst)).curry

theorem shift_measurePreserving (offset : Spatial) :
    MeasurePreserving (shiftFamily offset) (volume : Measure Spatial) volume := by
  change MeasurePreserving (fun point : Spatial => point - offset) volume volume
  simpa only [sub_eq_add_neg] using
    measurePreserving_add_right (volume : Measure Spatial) (-offset)

theorem shift_univ_measurePreserving (offset : Spatial) :
    MeasurePreserving (shiftFamily offset) (volume.restrict (Set.univ : Set Spatial))
      (volume.restrict (Set.univ : Set Spatial)) := by
  simpa only [Measure.restrict_univ] using shift_measurePreserving offset

def translation (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    (offset : Spatial) : PlaneL2 Value →ₗᵢ[ℂ] PlaneL2 Value :=
  Lp.compMeasurePreservingₗᵢ ℂ (shiftFamily offset) (shift_univ_measurePreserving offset)

def canonicalToVolume (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value] :
    PlaneL2 Value ≃ₗᵢ[ℂ] Lp Value 2 (volume : Measure Spatial) := by
  change Lp Value 2 (volume.restrict (Set.univ : Set Spatial)) ≃ₗᵢ[ℂ] Lp Value 2 volume
  rw [Measure.restrict_univ]
  exact LinearIsometryEquiv.refl ℂ _

def valueMap (Value : Type valueUniverse) (Other : Type otherUniverse)
    [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [NormedAddCommGroup Other] [InnerProductSpace ℂ Other] (mapping : Value →L[ℂ] Other) :
    PlaneL2 Value →L[ℂ] PlaneL2 Other :=
  mapping.compLpL 2 (volume.restrict (Set.univ : Set Spatial))

def kernelL1 (kernel : Spatial → ℝ) : ℝ := ∫ offset : Spatial, |kernel offset|

def average (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ) (field : PlaneL2 Value) : PlaneL2 Value :=
  ∫ offset : Spatial, kernel offset • translation Value offset field

def IsometryGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value],
    (∀ field : PlaneL2 Value, translation Value 0 field = field) ∧
    (∀ (first second : Spatial) (field : PlaneL2 Value),
      translation Value first (translation Value second field) = translation Value (first + second) field) ∧
    (∀ (offset : Spatial) (field : PlaneL2 Value),
      translation Value (-offset) (translation Value offset field) = field ∧
      translation Value offset (translation Value (-offset) field) = field) ∧
    (∀ (offset : Spatial) (field : PlaneL2 Value), ‖translation Value offset field‖ = ‖field‖) ∧
    (∀ (offset : Spatial) (field : PlaneL2 Value),
      translation Value offset field =ᵐ[(volume : Measure Spatial)] fun point => field (point - offset)) ∧
    (∀ offset : Spatial, ∃ equivalence : PlaneL2 Value ≃ₗᵢ[ℂ] PlaneL2 Value,
      (∀ field, equivalence field = translation Value offset field) ∧
      (∀ field, equivalence.symm field = translation Value (-offset) field))

def ContinuityGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value],
    Continuous (fun pair : Spatial × PlaneL2 Value => translation Value pair.1 pair.2) ∧
    (∀ field : PlaneL2 Value, Continuous (fun offset : Spatial => translation Value offset field)) ∧
    (∀ field : PlaneL2 Value,
      Filter.Tendsto (fun offset : Spatial => translation Value offset field) (𝓝 0) (𝓝 field))

def NaturalityGoal : Prop :=
  ∀ (Value : Type valueUniverse) (Other : Type otherUniverse)
    [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [NormedAddCommGroup Other] [InnerProductSpace ℂ Other]
    (mapping : Value →L[ℂ] Other) (offset : Spatial) (field : PlaneL2 Value),
    valueMap Value Other mapping (translation Value offset field) =
      translation Other offset (valueMap Value Other mapping field)

def CanonicalGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value],
    (∀ field : DomainL2 Value Set.univ,
      ‖canonicalToVolume Value field‖ = ‖field‖ ∧
      canonicalToVolume Value field =ᵐ[(volume : Measure Spatial)] field) ∧
    (∀ (offset : Spatial) (field : DomainL2 Value Set.univ),
      canonicalToVolume Value (translation Value offset field) =
        Lp.compMeasurePreserving (shiftFamily offset) (shift_measurePreserving offset)
          (canonicalToVolume Value field))

def AveragingGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), Integrable kernel volume →
    (∀ field : PlaneL2 Value,
      Integrable (fun offset : Spatial => kernel offset • translation Value offset field) volume) ∧
    (∀ field : PlaneL2 Value, ‖average Value kernel field‖ ≤ kernelL1 kernel * ‖field‖) ∧
    (∀ first second : PlaneL2 Value,
      average Value kernel (first + second) = average Value kernel first + average Value kernel second) ∧
    (∀ (scalar : ℂ) (field : PlaneL2 Value),
      average Value kernel (scalar • field) = scalar • average Value kernel field) ∧
    (∃ averaging : PlaneL2 Value →L[ℂ] PlaneL2 Value,
      (∀ field, averaging field = average Value kernel field) ∧ ‖averaging‖ ≤ kernelL1 kernel)

def FunctionalGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), Integrable kernel volume →
    ∀ (functional : PlaneL2 Value →L[ℂ] ℂ) (field : PlaneL2 Value),
      Integrable (fun offset : Spatial => kernel offset • functional (translation Value offset field)) volume ∧
      functional (average Value kernel field) =
        ∫ offset : Spatial, kernel offset • functional (translation Value offset field)

def CompactTestGoal : Prop :=
  ∀ (dimension : ℕ) (kernel : Spatial → ℝ), Integrable kernel volume →
    ∀ (field : FieldL2 dimension Set.univ) (cell : ℤ) (vector : PhysicalValue dimension)
      (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test),
      Integrable (fun offset : Spatial => kernel offset •
        (∫ point : Spatial, test point • inner ℂ vector (field (point - offset) cell))) volume ∧
      Grad.WeakTesting.compactPairing dimension Set.univ cell vector test smooth compact
          (average (CellValues dimension) kernel field) =
        ∫ offset : Spatial, kernel offset •
          (∫ point : Spatial, test point • inner ℂ vector (field (point - offset) cell))

def ContractionGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), Integrable kernel volume →
    (∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset) → (∫ offset, kernel offset) = 1 →
    (∀ field : PlaneL2 Value, ‖average Value kernel field‖ ≤ ‖field‖) ∧
    (∀ averaging : PlaneL2 Value →L[ℂ] PlaneL2 Value,
      (∀ field, averaging field = average Value kernel field) → ‖averaging‖ ≤ 1)

def ErrorGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (kernel : Spatial → ℝ), Integrable kernel volume →
    (∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset) → (∫ offset, kernel offset) = 1 →
    ∀ field : PlaneL2 Value,
      Integrable (fun offset : Spatial => kernel offset * ‖translation Value offset field - field‖) volume ∧
      ‖average Value kernel field - field‖ ≤
        ∫ offset : Spatial, kernel offset * ‖translation Value offset field - field‖

def SmallSupportGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    [CompleteSpace Value] (field : PlaneL2 Value) (tolerance : ℝ), 0 < tolerance →
    ∃ radius : ℝ, 0 < radius ∧
      ∀ kernel : Spatial → ℝ, Integrable kernel volume →
        (∀ᵐ offset ∂(volume : Measure Spatial), 0 ≤ kernel offset) → (∫ offset, kernel offset) = 1 →
        (∀ᵐ offset ∂(volume : Measure Spatial), kernel offset ≠ 0 → ‖offset‖ < radius) →
        ‖average Value kernel field - field‖ < tolerance

def CellGoal : Prop :=
  ∀ (dimension : ℕ) (offset : Spatial) (field : FieldL2 dimension Set.univ),
    ‖translation (CellValues dimension) offset field‖ = ‖field‖ ∧
    (∀ᵐ point ∂(volume : Measure Spatial), ∀ (cell : ℤ) (physical : Fin dimension),
      translation (CellValues dimension) offset field point cell physical = field (point - offset) cell physical) ∧
    (∀ cell : ℤ,
      Grad.GenericCarriers.fieldCellProjection dimension Set.univ cell
          (translation (CellValues dimension) offset field) =
        translation (PhysicalValue dimension) offset
          (Grad.GenericCarriers.fieldCellProjection dimension Set.univ cell field))

def BlockGoal : Prop :=
  IsometryGoal.{valueUniverse} ∧ ContinuityGoal.{valueUniverse} ∧
    NaturalityGoal.{valueUniverse, otherUniverse} ∧ CanonicalGoal.{valueUniverse} ∧
    AveragingGoal.{valueUniverse} ∧ FunctionalGoal.{valueUniverse} ∧ CompactTestGoal ∧
    ContractionGoal.{valueUniverse} ∧ ErrorGoal.{valueUniverse} ∧ SmallSupportGoal.{valueUniverse} ∧ CellGoal

end Grad.SpatialTranslation
