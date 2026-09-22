import BesselWeights
import Mathlib.Analysis.Normed.Module.TransferInstance

noncomputable section

namespace Grad.SobolevBridge

open Grad.PDEBootstrap MeasureTheory FourierTransform

structure Sobolev (order : ℝ) where
  coordinate : FieldL2

def sobolevEquiv (order : ℝ) : Sobolev order ≃ FieldL2 where
  toFun := Sobolev.coordinate
  invFun := Sobolev.mk
  left_inv field := by cases field; rfl
  right_inv field := rfl

instance sobolevNormedAddCommGroup (order : ℝ) : NormedAddCommGroup (Sobolev order) :=
  (sobolevEquiv order).normedAddCommGroup

instance sobolevModule (order : ℝ) : Module ℂ (Sobolev order) :=
  (sobolevEquiv order).module ℂ

instance sobolevNormedSpace (order : ℝ) : NormedSpace ℂ (Sobolev order) :=
  (sobolevEquiv order).normedSpace ℂ

def sobolevCoordinates (order : ℝ) : Sobolev order ≃ₗᵢ[ℂ] FieldL2 :=
  { (sobolevEquiv order).linearEquiv ℂ with norm_map' := fun _ => rfl }

instance sobolevCompleteSpace (order : ℝ) : CompleteSpace (Sobolev order) :=
  (sobolevCoordinates order).toIsometryEquiv.completeSpace_iff.mpr inferInstance

def sobolevDistribution (order : ℝ) : Sobolev order →L[ℂ] FieldDistribution :=
  weightedEmbedding (-order / 2) ∘L (sobolevCoordinates order).toContinuousLinearEquiv.toContinuousLinearMap

theorem sobolevDistribution_injective (order : ℝ) : Function.Injective (sobolevDistribution order) :=
  (weightedEmbedding_injective (-order / 2)).comp (sobolevCoordinates order).injective

theorem sobolevDistribution_recover (order : ℝ) (field : Sobolev order) :
    distributionWeight (order / 2) (sobolevDistribution order field) =
      distributionEmbedding (sobolevCoordinates order field) := by
  change distributionWeight (order / 2)
    (distributionWeight (-order / 2) (distributionEmbedding (sobolevCoordinates order field))) = _
  rw [distributionWeight_add]
  have exponentZero : order / 2 + -order / 2 = 0 := by ring
  rw [exponentZero, distributionWeight_zero]

theorem sobolevDistribution_range_iff (order : ℝ) (field : FieldDistribution) :
    field ∈ Set.range (sobolevDistribution order) ↔
      distributionWeight (order / 2) field ∈ Set.range distributionEmbedding := by
  constructor
  · rintro ⟨representative, rfl⟩
    exact ⟨sobolevCoordinates order representative, (sobolevDistribution_recover order representative).symm⟩
  · rintro ⟨representative, equality⟩
    refine ⟨(sobolevCoordinates order).symm representative, ?_⟩
    apply distributionWeight_injective (order / 2)
    rw [sobolevDistribution_recover, LinearIsometryEquiv.apply_symm_apply, equality]

theorem sobolev_weighted_fourier (order : ℝ) (field : Sobolev order) :
    TemperedDistribution.smulLeftCLM CellValues (weightSymbol (order / 2))
      (𝓕 (sobolevDistribution order field)) =
        distributionEmbedding (𝓕 (sobolevCoordinates order field) : FieldL2) := by
  have recovery := congrArg (fun distribution : FieldDistribution => 𝓕 distribution)
    (sobolevDistribution_recover order field)
  change 𝓕 (𝓕⁻ (TemperedDistribution.smulLeftCLM CellValues (weightSymbol (order / 2))
    (𝓕 (sobolevDistribution order field)))) =
      𝓕 (distributionEmbedding (sobolevCoordinates order field)) at recovery
  rw [fourier_fourierInv_eq] at recovery
  exact recovery.trans (Lp.fourier_toTemperedDistribution_eq _)

theorem sobolev_weighted_fourier_norm (order : ℝ) (field : Sobolev order) :
    ‖(𝓕 (sobolevCoordinates order field) : FieldL2)‖ = ‖field‖ := by
  rw [Lp.norm_fourier_eq, LinearIsometryEquiv.norm_map]

def sobolevShift (sourceOrder targetOrder : ℝ) : Sobolev sourceOrder ≃ₗᵢ[ℂ] Sobolev targetOrder :=
  (sobolevCoordinates sourceOrder).trans (sobolevCoordinates targetOrder).symm

theorem sobolevShift_distribution (sourceOrder targetOrder : ℝ) (field : Sobolev sourceOrder) :
    sobolevDistribution targetOrder (sobolevShift sourceOrder targetOrder field) =
      distributionWeight ((sourceOrder - targetOrder) / 2) (sobolevDistribution sourceOrder field) := by
  change distributionWeight (-targetOrder / 2) (distributionEmbedding field.coordinate) =
    distributionWeight ((sourceOrder - targetOrder) / 2)
      (distributionWeight (-sourceOrder / 2) (distributionEmbedding field.coordinate))
  rw [distributionWeight_add]
  have exponentIdentity : (sourceOrder - targetOrder) / 2 + -sourceOrder / 2 = -targetOrder / 2 := by ring
  rw [exponentIdentity]

def sobolevResolvent : Sobolev (-1) ≃ₗᵢ[ℂ] Sobolev 1 := sobolevShift (-1) 1

theorem sobolevResolvent_distribution (field : Sobolev (-1)) :
    sobolevDistribution 1 (sobolevResolvent field) =
      distributionResolvent (sobolevDistribution (-1) field) := by
  rw [sobolevResolvent, sobolevShift_distribution]
  norm_num
  rw [distributionWeight_neg_one]

theorem sobolevResolvent_norm (field : Sobolev (-1)) : ‖sobolevResolvent field‖ = ‖field‖ :=
  sobolevResolvent.norm_map field

end Grad.SobolevBridge
