import TensorSymbols
import HilbertLift

noncomputable section

namespace Grad.TensorBootstrap

open Grad.PDEBootstrap Grad.SobolevBridge

abbrev TensorL2 := FiniteL2 TensorIndex
abbrev TensorH1 := PiLp 2 (fun _ : TensorIndex => FieldH1)

abbrev tensorH1NormedSpace : NormedSpace ℂ TensorH1 :=
  PiLp.normedSpace (𝕜 := ℂ) (p := 2) (β := fun _ : TensorIndex => FieldH1)

attribute [local instance] tensorH1NormedSpace

def distributionDivDiv (tensor : TensorIndex → FieldDistribution) : FieldDistribution :=
  ∑ index, distributionDerivative index.1 (distributionDerivative index.2 (tensor index))

def tensorL2Resolvent : TensorL2 →L[ℂ] FieldL2 := l2Row tensorSymbol tensorSymbol_memLp

theorem tensorL2Resolvent_norm_le (tensor : TensorL2) : ‖tensorL2Resolvent tensor‖ ≤ ‖tensor‖ :=
  l2Row_norm_le tensorSymbol tensorSymbol_memLp tensorSymbol_row_bound tensor

theorem tensorL2Resolvent_opNorm_le : ‖tensorL2Resolvent‖ ≤ 1 :=
  l2Row_opNorm_le tensorSymbol tensorSymbol_memLp tensorSymbol_row_bound

theorem tensorL2Resolvent_distribution (tensor : TensorL2) :
    distributionEmbedding (tensorL2Resolvent tensor) =
      distributionResolvent (distributionDivDiv (fun index => distributionEmbedding (tensor index))) := by
  rw [tensorL2Resolvent, l2Row_distribution tensorSymbol tensorSymbol_memLp tensorSymbol_temperate,
    distributionDivDiv, map_sum]
  apply Finset.sum_congr rfl
  intro index membership
  exact tensorSymbol_distribution index _

def tensorValueInclusion : TensorH1 →L[ℂ] TensorL2 := hilbertLift valueInclusion

theorem tensorValueInclusion_apply (tensor : TensorH1) (index : TensorIndex) :
    tensorValueInclusion tensor index = valueInclusion (tensor index) := rfl

theorem tensorValueInclusion_norm_le (tensor : TensorH1) : ‖tensorValueInclusion tensor‖ ≤ ‖tensor‖ :=
  hilbertLift_norm_le valueInclusion valueInclusion_opNorm_le tensor

def tensorCoordinates : TensorH1 ≃ₗᵢ[ℂ] TensorL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : TensorIndex => halfGraphEquiv.symm)

theorem tensorCoordinates_recover (tensor : TensorH1) (index : TensorIndex) :
    halfL2 (tensorCoordinates tensor index) = valueInclusion (tensor index) := by
  change valueInclusion (halfGraphEquiv (halfGraphEquiv.symm (tensor index))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

def tensorH1Resolvent : TensorH1 →L[ℂ] FieldH1 :=
  halfGraphEquiv.toLinearIsometry.toContinuousLinearMap ∘L tensorL2Resolvent ∘L
    tensorCoordinates.toLinearIsometry.toContinuousLinearMap

theorem tensorH1Resolvent_norm_le (tensor : TensorH1) : ‖tensorH1Resolvent tensor‖ ≤ ‖tensor‖ := by
  change ‖halfGraphEquiv (tensorL2Resolvent (tensorCoordinates tensor))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (tensorL2Resolvent_norm_le _).trans_eq (tensorCoordinates.norm_map tensor)

theorem tensorH1Resolvent_opNorm_le : ‖tensorH1Resolvent‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro tensor
  simpa only [one_mul] using tensorH1Resolvent_norm_le tensor

set_option maxHeartbeats 800000 in
theorem tensorH1Resolvent_value (tensor : TensorH1) :
    valueInclusion (tensorH1Resolvent tensor) = tensorL2Resolvent (tensorValueInclusion tensor) := by
  apply distributionEmbedding_injective
  change distributionEmbedding (halfL2 (tensorL2Resolvent (tensorCoordinates tensor))) = _
  rw [halfL2_distribution]
  simp only [tensorL2Resolvent, l2Row_distribution tensorSymbol tensorSymbol_memLp tensorSymbol_temperate]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index membership
  change TemperedDistribution.fourierMultiplierCLM CellValues halfSymbol
    (TemperedDistribution.fourierMultiplierCLM CellValues (tensorSymbol index)
      (distributionEmbedding (tensorCoordinates tensor index))) =
    TemperedDistribution.fourierMultiplierCLM CellValues (tensorSymbol index)
      (distributionEmbedding (valueInclusion (tensor index)))
  rw [distributionMultiplier_comp halfSymbol_temperate (tensorSymbol_temperate index),
    mul_comm halfSymbol, ← distributionMultiplier_comp (tensorSymbol_temperate index) halfSymbol_temperate]
  change TemperedDistribution.fourierMultiplierCLM CellValues (tensorSymbol index)
    (distributionWeight (-1 / 2) (distributionEmbedding (tensorCoordinates tensor index))) = _
  rw [← halfL2_distribution, tensorCoordinates_recover]

theorem tensorH1Resolvent_compatible :
    valueInclusion ∘L tensorH1Resolvent = tensorL2Resolvent ∘L tensorValueInclusion := by
  apply ContinuousLinearMap.ext
  exact tensorH1Resolvent_value

theorem tensorH1Resolvent_distribution (tensor : TensorH1) :
    distributionEmbedding (valueInclusion (tensorH1Resolvent tensor)) =
      distributionResolvent (distributionDivDiv (fun index => distributionEmbedding (valueInclusion (tensor index)))) := by
  rw [tensorH1Resolvent_value, tensorL2Resolvent_distribution]
  rfl

abbrev DerivativeIndex (rank : ℕ) := Fin rank → Fin 2

def tensorL2RankLift (rank : ℕ) :
    PiLp 2 (fun _ : DerivativeIndex rank => TensorL2) →L[ℂ]
      PiLp 2 (fun _ : DerivativeIndex rank => FieldL2) := hilbertLift tensorL2Resolvent

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
def tensorH1RankLift (rank : ℕ) :
    PiLp 2 (fun _ : DerivativeIndex rank => TensorH1) →L[ℂ]
      PiLp 2 (fun _ : DerivativeIndex rank => FieldH1) :=
  hilbertLift (Scalar := ℂ) (Index := DerivativeIndex rank) (Input := TensorH1) (Output := FieldH1) tensorH1Resolvent

theorem tensorL2RankLift_opNorm_le (rank : ℕ) : ‖tensorL2RankLift rank‖ ≤ 1 :=
  (hilbertLift_opNorm_le tensorL2Resolvent).trans tensorL2Resolvent_opNorm_le

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem tensorH1RankLift_opNorm_le (rank : ℕ) : ‖tensorH1RankLift rank‖ ≤ 1 :=
  (hilbertLift_opNorm_le (Scalar := ℂ) (Index := DerivativeIndex rank) tensorH1Resolvent).trans
    tensorH1Resolvent_opNorm_le

end Grad.TensorBootstrap
