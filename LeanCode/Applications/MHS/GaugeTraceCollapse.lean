import GaugeSplittings

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

theorem valueMapJet_smul_map {sourceDimension targetDimension : ℕ}
    (scalar : ℂ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) :
    valueMapJet (scalar • mapping) field = scalar • valueMapJet mapping field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value, smul_apply, closedJet_value_smul,
    ContinuousMap.smul_apply]

theorem reflectedVectorJet_add (first second : ClosedJet 2) :
    reflectedVectorJet (first + second) =
      reflectedVectorJet first + reflectedVectorJet second :=
  reflectedVectorLinear.map_add first second

theorem valueMapJet_sub_field {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (first second : ClosedJet sourceDimension) :
    valueMapJet mapping (first - second) =
      valueMapJet mapping first - valueMapJet mapping second :=
  (valueMapJetLinear _ _ mapping).map_sub first second

theorem valueMapJet_smul_field {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (scalar : ℂ) (field : ClosedJet sourceDimension) :
    valueMapJet mapping (scalar • field) = scalar • valueMapJet mapping field :=
  (valueMapJetLinear _ _ mapping).map_smul scalar field

/-- Sandwiching an arbitrary constant value operator between two equivariant
averages keeps only the two helicity-diagonal coefficients. -/
theorem equivariant_valueMap_sandwich
    (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) (field : ClosedJet 2) :
    equivariantAverageJet (valueMapJet mapping (equivariantAverageJet field)) =
      alphaPlus mapping • valueMapJet positiveHelicity (angularClosedJet 1 field) +
        alphaMinus mapping • valueMapJet negativeHelicity (angularClosedJet (-1) field) := by
  rw [equivariantAverageJet_eq field, valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    equivariantAverageJet_eq]
  simp only [angularClosedJet_add, angularClosedJet_valueMap, angularClosedJet_projection]
  norm_num
  rw [valueMapJet_map_zero, valueMapJet_map_zero, add_zero, zero_add, valueMapJet_comp,
    valueMapJet_comp, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc positiveHelicity mapping positiveHelicity,
    ContinuousLinearMap.comp_assoc negativeHelicity mapping negativeHelicity,
    positiveHelicity_conjugation, negativeHelicity_conjugation,
    valueMapJet_smul_map, valueMapJet_smul_map]

/-- The reflected counterpart of the sandwich identity. -/
theorem reflected_equivariant_sandwich
    (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) (field : ClosedJet 2) :
    equivariantAverageJet (valueMapJet mapping (reflectedVectorJet (equivariantAverageJet field))) =
      alphaPlus mapping • reflectedVectorJet
          (valueMapJet negativeHelicity (angularClosedJet (-1) field)) +
        alphaMinus mapping • reflectedVectorJet
          (valueMapJet positiveHelicity (angularClosedJet 1 field)) := by
  have orthogonalAdd (first second : ClosedJet 2) :
      orthogonalJet cartesianReflectionEquiv (first + second) =
        orthogonalJet cartesianReflectionEquiv first +
          orthogonalJet cartesianReflectionEquiv second :=
    (orthogonalJetLinear 2 cartesianReflectionEquiv).map_add first second
  have reflectedExpansion :
      reflectedVectorJet (equivariantAverageJet field) =
        valueMapJet (reflectionValueMap.comp positiveHelicity)
            (angularClosedJet (-1) (orthogonalJet cartesianReflectionEquiv field)) +
          valueMapJet (reflectionValueMap.comp negativeHelicity)
            (angularClosedJet 1 (orthogonalJet cartesianReflectionEquiv field)) := by
    rw [reflectedVectorJet_eq, equivariantAverageJet_eq, orthogonalAdd,
      ← valueMapJet_orthogonal, ← valueMapJet_orthogonal,
      angularClosedJet_reflection, angularClosedJet_reflection, valueMapJet_add,
      valueMapJet_comp, valueMapJet_comp]
    norm_num
  rw [reflectedExpansion, valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    equivariantAverageJet_eq]
  simp only [angularClosedJet_add, angularClosedJet_valueMap, angularClosedJet_projection]
  norm_num
  rw [valueMapJet_map_zero, valueMapJet_map_zero, add_zero, zero_add,
    valueMapJet_comp, valueMapJet_comp]
  have positiveWord :
      positiveHelicity.comp (mapping.comp (reflectionValueMap.comp negativeHelicity)) =
        alphaPlus mapping • (reflectionValueMap.comp negativeHelicity) := by
    rw [reflectionValue_negative, ← ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc positiveHelicity mapping positiveHelicity,
      positiveHelicity_conjugation, ContinuousLinearMap.smul_comp,
      ← reflectionValue_negative]
  have negativeWord :
      negativeHelicity.comp (mapping.comp (reflectionValueMap.comp positiveHelicity)) =
        alphaMinus mapping • (reflectionValueMap.comp positiveHelicity) := by
    rw [reflectionValue_positive, ← ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc negativeHelicity mapping negativeHelicity,
      negativeHelicity_conjugation, ContinuousLinearMap.smul_comp,
      ← reflectionValue_positive]
  rw [positiveWord, negativeWord, valueMapJet_smul_map, valueMapJet_smul_map]
  have reflectedNegative :
      valueMapJet (reflectionValueMap.comp negativeHelicity)
          (angularClosedJet 1 (orthogonalJet cartesianReflectionEquiv field)) =
        reflectedVectorJet (valueMapJet negativeHelicity (angularClosedJet (-1) field)) := by
    rw [reflectedVectorJet_eq, ← valueMapJet_orthogonal, angularClosedJet_reflection,
      valueMapJet_comp]
    norm_num
  have reflectedPositive :
      valueMapJet (reflectionValueMap.comp positiveHelicity)
          (angularClosedJet (-1) (orthogonalJet cartesianReflectionEquiv field)) =
        reflectedVectorJet (valueMapJet positiveHelicity (angularClosedJet 1 field)) := by
    rw [reflectedVectorJet_eq, ← valueMapJet_orthogonal, angularClosedJet_reflection,
      valueMapJet_comp]
  rw [reflectedNegative, reflectedPositive]

/-- The literal N13 trace collapse: sandwiching any constant value operator
between two tangential projections multiplies by half the operator trace. -/
theorem tangentialJet_valueMap_collapse
    (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) (field : ClosedJet 2) :
    tangentialJet (valueMapJet mapping (tangentialJet field)) =
      (operatorTrace mapping / 2) • tangentialJet field := by
  have innerExpansion :
      valueMapJet mapping (tangentialJet field) = (1 / 2 : ℂ) •
        (valueMapJet mapping (equivariantAverageJet field) -
          valueMapJet mapping (reflectedVectorJet (equivariantAverageJet field))) := by
    rw [tangentialJet_eq, valueMapJet_smul_field, valueMapJet_sub_field]
  have averaged :
      equivariantAverageJet (valueMapJet mapping (tangentialJet field)) = (1 / 2 : ℂ) •
        ((alphaPlus mapping • valueMapJet positiveHelicity (angularClosedJet 1 field) +
            alphaMinus mapping • valueMapJet negativeHelicity (angularClosedJet (-1) field)) -
          (alphaPlus mapping • reflectedVectorJet
              (valueMapJet negativeHelicity (angularClosedJet (-1) field)) +
            alphaMinus mapping • reflectedVectorJet
              (valueMapJet positiveHelicity (angularClosedJet 1 field)))) := by
    rw [innerExpansion, equivariantAverageJet_smul, equivariantAverageJet_sub,
      equivariant_valueMap_sandwich, reflected_equivariant_sandwich]
  rw [tangentialJet_eq, averaged, tangentialJet_eq, equivariantAverageJet_eq]
  rw [reflectedVectorJet_smul]
  have reflectedAveraged :
      reflectedVectorJet
          ((alphaPlus mapping • valueMapJet positiveHelicity (angularClosedJet 1 field) +
              alphaMinus mapping • valueMapJet negativeHelicity (angularClosedJet (-1) field)) -
            (alphaPlus mapping • reflectedVectorJet
                (valueMapJet negativeHelicity (angularClosedJet (-1) field)) +
              alphaMinus mapping • reflectedVectorJet
                (valueMapJet positiveHelicity (angularClosedJet 1 field)))) =
        (alphaPlus mapping • reflectedVectorJet
            (valueMapJet positiveHelicity (angularClosedJet 1 field)) +
          alphaMinus mapping • reflectedVectorJet
            (valueMapJet negativeHelicity (angularClosedJet (-1) field))) -
        (alphaPlus mapping • valueMapJet negativeHelicity (angularClosedJet (-1) field) +
          alphaMinus mapping • valueMapJet positiveHelicity (angularClosedJet 1 field)) := by
    rw [reflectedVectorJet_sub, reflectedVectorJet_add, reflectedVectorJet_add,
      reflectedVectorJet_smul,
      reflectedVectorJet_smul, reflectedVectorJet_smul, reflectedVectorJet_smul,
      reflectedVectorJet_involutive, reflectedVectorJet_involutive]
  rw [reflectedAveraged, reflectedVectorJet_add]
  have traceSplit : operatorTrace mapping = alphaPlus mapping + alphaMinus mapping :=
    (alphaPlus_add_alphaMinus mapping).symm
  rw [traceSplit]
  module

/-- Grade-core version of the trace collapse, including a cell shift. -/
theorem tangentialGradeCore_mode_collapse {grade : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (field : GradeCore parameters 2 grade) :
    tangentialGradeCore parameters (singleModeGradeCore parameters shift mapping
        (tangentialGradeCore parameters field)) =
      (operatorTrace mapping / 2) • singleModeGradeCore parameters shift
        (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) (tangentialGradeCore parameters field) := by
  apply GradeCore.toCore_injective
  apply Subtype.ext
  funext cell
  change tangentialJet (valueMapJet mapping
      ((tangentialCore parameters field.toCore).1 (cell - shift))) =
    ((operatorTrace mapping / 2) • valueMapJet (ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
      ((tangentialCore parameters field.toCore).1 (cell - shift)) : ClosedJet 2)
  rw [tangentialCore_apply, valueMapJet_id]
  exact tangentialJet_valueMap_collapse mapping (field.toCore.1 (cell - shift))

/-- Completed version of the trace collapse for a single completed mode. -/
theorem tangentialCompleted_mode_collapse {grade : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    (tangentialCompleted (grade := grade) parameters).comp
        ((singleModeCompleted parameters shift mapping).comp (tangentialCompleted parameters)) =
      (operatorTrace mapping / 2) •
        (singleModeCompleted parameters shift (ContinuousLinearMap.id ℂ (ComplexEuclidean 2))).comp
          (tangentialCompleted parameters) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    tangentialCompleted_eta, singleModeCompleted_eta, tangentialCompleted_eta,
    smul_apply, ContinuousLinearMap.comp_apply,
    tangentialCompleted_eta, singleModeCompleted_eta,
    tangentialGradeCore_mode_collapse, map_smul]

end Grad.Constraints.Gauges
