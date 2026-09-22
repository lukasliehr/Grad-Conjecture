import EquivariantAverageProjection

noncomputable section

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

def closedDerivativeLinear {dimension : ℕ} (order : ℕ) (word : CartesianWord order) :
    ClosedJet dimension →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) where
  toFun field := closedDerivative field order word
  map_add' first second := by
    change closedDerivative (closedJetAdd first second) order word = _
    rw [closedJetAdd_derivative]
    rfl
  map_smul' scalar field := by
    change closedDerivative (closedJetSmul scalar field) order word = _
    rw [closedJetSmul_derivative]
    rfl

theorem valueMapJet_preserves_zero_derivatives {sourceDimension targetDimension order : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (valueMapJet mapping field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
  rw [valueMapJet_derivative]
  change mapping (closedDerivative field order word _) = 0
  rw [zeroJets, map_zero]

theorem equivariantAverageJet_preserves_zero_derivatives {order : ℕ} (field : ClosedJet 2)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (equivariantAverageJet field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
  rw [equivariantAverageJet_eq]
  change (closedDerivativeLinear order word (_ + _)) _ = 0
  rw [map_add, ContinuousMap.add_apply]
  have first := valueMapJet_preserves_zero_derivatives positiveHelicity _
    (angularClosedJet_preserves_zero_derivatives 1 field zeroJets) word
  have second := valueMapJet_preserves_zero_derivatives negativeHelicity _
    (angularClosedJet_preserves_zero_derivatives (-1) field zeroJets) word
  exact (congrArg₂ (· + ·) first second).trans (zero_add 0)

theorem reflectedVectorJet_preserves_zero_derivatives {order : ℕ} (field : ClosedJet 2)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (reflectedVectorJet field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 :=
  valueMapJet_preserves_zero_derivatives reflectionValueMap _
    (orthogonalJet_preserves_zero_derivatives cartesianReflectionEquiv field zeroJets) word

theorem tangentialJet_preserves_zero_derivatives {order : ℕ} (field : ClosedJet 2)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (tangentialJet field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
  rw [tangentialJet_eq]
  change (closedDerivativeLinear order word ((1 / 2 : ℂ) • (_ - _))) _ = 0
  rw [map_smul, map_sub, ContinuousMap.smul_apply, ContinuousMap.sub_apply]
  have first := equivariantAverageJet_preserves_zero_derivatives field zeroJets
  have second := reflectedVectorJet_preserves_zero_derivatives _ first
  change (1 / 2 : ℂ) • (closedDerivative (equivariantAverageJet field) order word _ -
    closedDerivative (reflectedVectorJet (equivariantAverageJet field)) order word _) = 0
  rw [first word, second word, sub_self, smul_zero]

end Grad.Constraints
