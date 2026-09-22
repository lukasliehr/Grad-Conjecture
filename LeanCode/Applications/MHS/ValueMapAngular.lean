import ClosedJetValueMap
import AngularProjectionMaps

noncomputable section

open Set MeasureTheory
open scoped Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Radial

theorem valueMapJet_add {firstDimension secondDimension : ℕ}
    (mapping : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension)
    (first second : ClosedJet firstDimension) :
    valueMapJet mapping (first + second) = valueMapJet mapping first + valueMapJet mapping second :=
  (valueMapJetLinear _ _ mapping).map_add first second

theorem valueMapJet_map_zero {firstDimension secondDimension : ℕ}
    (mapping : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension) :
    valueMapJet mapping 0 = 0 := (valueMapJetLinear _ _ mapping).map_zero

theorem valueMapJet_comp {firstDimension secondDimension thirdDimension : ℕ}
    (first : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension)
    (second : ComplexEuclidean secondDimension →L[ℂ] ComplexEuclidean thirdDimension)
    (field : ClosedJet firstDimension) :
    valueMapJet second (valueMapJet first field) = valueMapJet (second.comp first) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value, ContinuousLinearMap.comp_apply]

theorem valueMapJet_zero {firstDimension secondDimension : ℕ} (field : ClosedJet firstDimension) :
    valueMapJet (0 : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension) field = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value, zero_apply, closedJet_value_zero, ContinuousMap.zero_apply]

theorem valueMapJet_orthogonal {firstDimension secondDimension : ℕ}
    (mapping : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet firstDimension) :
    valueMapJet mapping (orthogonalJet orthogonal field) =
      orthogonalJet orthogonal (valueMapJet mapping field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value]
  exact (valueMapJet_value mapping field (orthogonalClosedPoint orthogonal point)).symm

theorem angularClosedJet_valueMap {firstDimension secondDimension : ℕ}
    (mapping : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension)
    (mode : ℤ) (field : ClosedJet firstDimension) :
    angularClosedJet mode (valueMapJet mapping field) =
      valueMapJet mapping (angularClosedJet mode field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value, valueMapJet_value, angularClosedJet_value]
  simp_rw [valueMapJet_value, ← map_smul]
  rw [mapping.intervalIntegral_comp_comm
    ((angularValueIntegrand_continuous mode field point).intervalIntegrable _ _)]
  exact ((mapping.restrictScalars ℝ).map_smul _ _).symm

end Grad.Constraints
