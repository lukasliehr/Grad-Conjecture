import ClosedJetSmoothExtension
import ClosedJetIntegralL2

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

def valueMapClosed {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : C(ClosedDisk, ComplexEuclidean sourceDimension)) :
    C(ClosedDisk, ComplexEuclidean targetDimension) :=
  ⟨fun point => mapping (field point), mapping.continuous.comp field.continuous⟩

def valueMapJet {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) : ClosedJet targetDimension :=
  globalClosedJet ((mapping.restrictScalars ℝ) ∘ smoothClosedExtension field)
    ((mapping.restrictScalars ℝ).contDiff.comp (smoothClosedExtension_smooth field))

@[simp] theorem valueMapJet_value {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) (point : ClosedDisk) :
    (valueMapJet mapping field).value point = mapping (field.value point) := by
  change mapping (smoothClosedExtension field point.val) = _
  rw [smoothClosedExtension_value]

theorem valueMapJet_derivative {sourceDimension targetDimension order : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) (word : CartesianWord order) :
    closedDerivative (valueMapJet mapping field) order word =
      valueMapClosed mapping (closedDerivative field order word) := by
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet, globalClosedJet_derivative]
  change (iteratedFDeriv ℝ order ((mapping.restrictScalars ℝ) ∘ smoothClosedExtension field)
    point.val) (fun position => spatialBasis (word position)) = _
  rw [(mapping.restrictScalars ℝ).iteratedFDeriv_comp_left
    (smoothClosedExtension_smooth field).contDiffAt
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  exact congrArg mapping (smoothClosedExtension_derivative field word point)

def valueMapJetLinear (sourceDimension targetDimension : ℕ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ClosedJet sourceDimension →ₗ[ℂ] ClosedJet targetDimension where
  toFun := valueMapJet mapping
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change (valueMapJet mapping (first + second)).value point =
      (valueMapJet mapping first).value point + (valueMapJet mapping second).value point
    simp only [valueMapJet_value, closedJet_value_add, ContinuousMap.add_apply, map_add]
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change (valueMapJet mapping (scalar • field)).value point = scalar • (valueMapJet mapping field).value point
    simp only [valueMapJet_value, closedJet_value_smul, ContinuousMap.smul_apply, map_smul]

theorem valueMapJet_phaseWeighted {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet sourceDimension) :
    valueMapJet mapping (phaseWeightedJet parameters cell field) =
      phaseWeightedJet parameters cell (valueMapJet mapping field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value, phaseWeightedJet_spec, phaseWeightedJet_spec, valueMapJet_value]
  exact (mapping.restrictScalars ℝ).map_smul _ _

theorem closedDiskLift_valueMapClosed {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : C(ClosedDisk, ComplexEuclidean sourceDimension)) :
    closedDiskLift (valueMapClosed mapping field) = mapping ∘ closedDiskLift field := by
  funext point
  by_cases inside : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, valueMapClosed, inside]

theorem closedValueL2_valueMap {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : C(ClosedDisk, ComplexEuclidean sourceDimension)) :
    closedContinuousToDiskL2 (valueMapClosed mapping field) =
      mapping.compLp (closedContinuousToDiskL2 field) := by
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (valueMapClosed mapping field),
    closedContinuousToDiskL2_ae field, mapping.coeFn_compLp (closedContinuousToDiskL2 field)]
    with point targetAt sourceAt mappedAt
  rw [targetAt, mappedAt, sourceAt]
  exact congrFun (closedDiskLift_valueMapClosed mapping field) point

theorem closedValueL2_valueMap_norm_le {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : C(ClosedDisk, ComplexEuclidean sourceDimension)) :
    ‖closedContinuousToDiskL2 (valueMapClosed mapping field)‖ ≤
      ‖mapping‖ * ‖closedContinuousToDiskL2 field‖ := by
  rw [closedValueL2_valueMap]
  exact mapping.norm_compLp_le _

end Grad.Constraints
