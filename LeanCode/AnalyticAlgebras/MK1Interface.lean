import WeakH1
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

noncomputable section

open MeasureTheory

namespace Grad.MatrixMultiplier

def multiplierSpec {Space ValueIn ValueOut : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
    [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]
    (measure : Measure Space) (coefficients : Space → ValueIn →L[ℂ] ValueOut) (bound : ℝ)
    (multiplier : Lp ValueIn 2 measure →L[ℂ] Lp ValueOut 2 measure) : Prop :=
  (∀ representative : Space → ValueIn, MemLp representative 2 measure →
    MemLp (fun point => coefficients point (representative point)) 2 measure) ∧
  ‖multiplier‖ ≤ bound ∧
  (∀ field, ‖multiplier field‖ ≤ bound * ‖field‖) ∧
  (∀ field : Lp ValueIn 2 measure,
    ∀ᵐ point ∂measure, multiplier field point = coefficients point (field point)) ∧
  (∀ (representative : Space → ValueIn) (membership : MemLp representative 2 measure),
    ∀ᵐ point ∂measure,
      multiplier (membership.toLp representative) point = coefficients point (representative point)) ∧
  (∀ (first second : Space → ValueIn)
      (firstMembership : MemLp first 2 measure) (secondMembership : MemLp second 2 measure),
    first =ᵐ[measure] second →
      multiplier (firstMembership.toLp first) = multiplier (secondMembership.toLp second)) ∧
  (∀ first second, multiplier (first + second) = multiplier first + multiplier second) ∧
  (∀ (scalar : ℂ) field, multiplier (scalar • field) = scalar • multiplier field)

def blockGoal {Space ValueIn ValueOut : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
    [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut] (measure : Measure Space) : Prop :=
  ∀ (coefficients : Space → ValueIn →L[ℂ] ValueOut) (bound : ℝ),
    AEStronglyMeasurable coefficients measure → 0 ≤ bound →
    (∀ᵐ point ∂measure, ‖coefficients point‖ ≤ bound) →
    ∃ multiplier : Lp ValueIn 2 measure →L[ℂ] Lp ValueOut 2 measure,
      multiplierSpec measure coefficients bound multiplier

def compositionGoal {Space ValueIn ValueMiddle ValueOut : Type*} [MeasurableSpace Space]
    [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
    [NormedAddCommGroup ValueMiddle] [NormedSpace ℂ ValueMiddle]
    [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut] (measure : Measure Space) : Prop :=
  ∀ (first : Space → ValueIn →L[ℂ] ValueMiddle)
    (second : Space → ValueMiddle →L[ℂ] ValueOut) (firstBound secondBound : ℝ),
    AEStronglyMeasurable first measure → AEStronglyMeasurable second measure →
    0 ≤ firstBound → 0 ≤ secondBound →
    (∀ᵐ point ∂measure, ‖first point‖ ≤ firstBound) →
    (∀ᵐ point ∂measure, ‖second point‖ ≤ secondBound) →
    ∃ firstMap : Lp ValueIn 2 measure →L[ℂ] Lp ValueMiddle 2 measure,
    ∃ secondMap : Lp ValueMiddle 2 measure →L[ℂ] Lp ValueOut 2 measure,
    ∃ compositeMap : Lp ValueIn 2 measure →L[ℂ] Lp ValueOut 2 measure,
      multiplierSpec measure first firstBound firstMap ∧
      multiplierSpec measure second secondBound secondMap ∧
      multiplierSpec measure (fun point => (second point).comp (first point))
        (secondBound * firstBound) compositeMap ∧
      compositeMap = secondMap.comp firstMap

def physicalConsumerGoal : Prop :=
  ∀ (inputDimension outputDimension : ℕ) (domain : Set Grad.PDEBootstrap.Spatial)
    (coefficients : Grad.PDEBootstrap.Spatial →
      EuclideanSpace ℂ (Fin inputDimension) →L[ℂ] EuclideanSpace ℂ (Fin outputDimension))
    (bound : ℝ),
    AEStronglyMeasurable coefficients (volume.restrict domain) → 0 ≤ bound →
    (∀ᵐ point ∂volume.restrict domain, ‖coefficients point‖ ≤ bound) →
    ∃ multiplier :
      Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin outputDimension)) 2 (volume.restrict domain),
      (∀ representative : Grad.PDEBootstrap.Spatial → EuclideanSpace ℂ (Fin inputDimension),
        MemLp representative 2 (volume.restrict domain) →
        MemLp (fun point => coefficients point (representative point)) 2 (volume.restrict domain)) ∧
      ‖multiplier‖ ≤ bound ∧
      (∀ field, ‖multiplier field‖ ≤ bound * ‖field‖) ∧
      (∀ field : Lp (EuclideanSpace ℂ (Fin inputDimension)) 2 (volume.restrict domain),
        ∀ᵐ point ∂volume.restrict domain, multiplier field point = coefficients point (field point)) ∧
      (∀ (representative : Grad.PDEBootstrap.Spatial → EuclideanSpace ℂ (Fin inputDimension))
          (membership : MemLp representative 2 (volume.restrict domain)),
        ∀ᵐ point ∂volume.restrict domain,
          multiplier (membership.toLp representative) point = coefficients point (representative point)) ∧
      (∀ (first second : Grad.PDEBootstrap.Spatial → EuclideanSpace ℂ (Fin inputDimension))
          (firstMembership : MemLp first 2 (volume.restrict domain))
          (secondMembership : MemLp second 2 (volume.restrict domain)),
        first =ᵐ[volume.restrict domain] second →
          multiplier (firstMembership.toLp first) = multiplier (secondMembership.toLp second)) ∧
      (∀ first second, multiplier (first + second) = multiplier first + multiplier second) ∧
      (∀ (scalar : ℂ) field, multiplier (scalar • field) = scalar • multiplier field)

end Grad.MatrixMultiplier
