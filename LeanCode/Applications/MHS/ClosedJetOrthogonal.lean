import GC13Orthogonal
import FC3LinearJet

noncomputable section

open Set Grad.ClosedJets Grad.CartesianState
open Grad.RepresentedKernel.SpatialProduct Grad.GaugeCoefficients.Radial
open scoped BigOperators ContDiff Topology

namespace Grad.Constraints

def orthogonalValue {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  ⟨fun point => field.value (orthogonalClosedPoint orthogonal point),
    field.value.continuous.comp (continuous_orthogonalClosedPoint orthogonal)⟩

theorem lift_orthogonalValue {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    closedDiskLift (orthogonalValue orthogonal field) =
      fun point => closedDiskLift field.value (orthogonal point) := by
  funext point
  have invariant : orthogonal point ∈ closedUnitDisk ↔ point ∈ closedUnitDisk := by
    change ‖orthogonal point‖ ≤ 1 ↔ ‖point‖ ≤ 1
    rw [orthogonal.norm_map]
  by_cases inside : point ∈ closedUnitDisk
  · simp only [closedDiskLift, inside, invariant.mpr inside, dite_true]
    rfl
  · simp only [closedDiskLift, inside, mt invariant.mp inside, dite_false]

def orthogonalDerivative {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) : C(ClosedDisk, ComplexEuclidean dimension) where
  toFun point := ∑ target : CartesianWord order,
    chainFactor order orthogonal word target •
      closedDerivative field order target (orthogonalClosedPoint orthogonal point)
  continuous_toFun := by
    apply continuous_finsetSum
    intro target _
    exact (continuous_const : Continuous (fun _ : ClosedDisk =>
      chainFactor order orthogonal word target)).smul ((closedDerivative field order target).continuous.comp
      (continuous_orthogonalClosedPoint orthogonal))

theorem orthogonalDerivative_spec {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (orthogonalValue orthogonal field) order word
      (orthogonalDerivative orthogonal field order word) := by
  intro point inside
  rw [lift_orthogonalValue]
  change _ = wordDerivative order word
    (fun source => closedDiskLift field.value (orthogonal source)) point.val
  rw [word_chain openUnitDisk openUnitDisk_isOpen orthogonal
    (openUnitDisk_invariant orthogonal) _ order word point.val inside, twisted_expansion]
  apply Finset.sum_congr rfl
  intro target _
  rw [closedDerivative_spec field order target (orthogonalClosedPoint orthogonal point)
    ((openUnitDisk_invariant orthogonal point.val).mpr inside)]
  rfl

/-- Literal disk pullback, preserving every boundary derivative jet. -/
def orthogonalJet {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    ClosedJet dimension where
  value := orthogonalValue orthogonal field
  smoothInterior := by
    rw [lift_orthogonalValue]
    exact field.smoothInterior.comp orthogonal.contDiff.contDiffOn
      (fun point inside => (openUnitDisk_invariant orthogonal point).mpr inside)
  derivativeExists order word :=
    ⟨orthogonalDerivative orthogonal field order word,
      orthogonalDerivative_spec orthogonal field order word⟩

theorem orthogonalJet_derivative {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    closedDerivative (orthogonalJet orthogonal field) order word =
      orthogonalDerivative orthogonal field order word :=
  (cartesianExtension_unique _ order word _
    (orthogonalDerivative_spec orthogonal field order word)).symm

def orthogonalJetLinear (dimension : ℕ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := orthogonalJet orthogonal
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    rfl
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    rfl

theorem orthogonalJet_refl {dimension : ℕ} (field : ClosedJet dimension) :
    orthogonalJet (LinearIsometryEquiv.refl ℝ SpatialPlane) field = field := by
  apply closedJet_eq_of_value_eq
  rfl

theorem orthogonalJet_trans {dimension : ℕ}
    (first second : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    orthogonalJet first (orthogonalJet second field) =
      orthogonalJet (first.trans second) field := by
  apply closedJet_eq_of_value_eq
  rfl

theorem orthogonalJet_preserves_zero_derivatives {dimension order : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (orthogonalJet orthogonal field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
  rw [orthogonalJet_derivative]
  change (∑ target : CartesianWord order, chainFactor order orthogonal word target •
    closedDerivative field order target (orthogonalClosedPoint orthogonal
      ⟨0, by simp [closedUnitDisk]⟩)) = 0
  have zeroPoint : orthogonalClosedPoint orthogonal ⟨0, by simp [closedUnitDisk]⟩ =
      ⟨0, by simp [closedUnitDisk]⟩ := by
    apply Subtype.ext
    exact map_zero orthogonal
  simp only [zeroPoint, zeroJets, smul_zero, Finset.sum_const_zero]

end Grad.Constraints
