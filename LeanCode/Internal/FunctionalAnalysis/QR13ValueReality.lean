import QR12MultiplierReality

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra

theorem valueMapCore_conjugate {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (mapping : OperatorValue sourceDimension targetDimension)
    (field : ACore parameters sourceDimension) :
    cartesianCoreConjugation parameters (valueMapCore mapping parameters field) =
      valueMapCore (operatorConjugation sourceDimension targetDimension mapping) parameters
        (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [cartesianCoreConjugation_apply, valueMapCore_apply,
    closedJetConjugate_value, valueMapJet_value, conjugateClosedMap_apply]
  change cartesianPhysicalConjugation targetDimension
      (mapping ((field.1 (-cell)).value point)) =
    operatorConjugation sourceDimension targetDimension mapping
      (cartesianPhysicalConjugation sourceDimension ((field.1 (-cell)).value point))
  exact (operatorConjugation_eval mapping _).symm

theorem operatorConjugation_comp {first second third : ℕ}
    (outer : OperatorValue second third) (inner : OperatorValue first second) :
    operatorConjugation first third (outer.comp inner) =
      (operatorConjugation second third outer).comp (operatorConjugation first second inner) := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation third
    (outer (inner (cartesianPhysicalConjugation first vector))) =
    cartesianPhysicalConjugation third (outer (cartesianPhysicalConjugation second
      (cartesianPhysicalConjugation second (inner (cartesianPhysicalConjugation first vector)))))
  rw [cartesianPhysicalConjugation_involutive]

theorem planarPartMap_conjugate : operatorConjugation 3 2 planarPartMap = planarPartMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 2 (planarPartMap (cartesianPhysicalConjugation 3 vector)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarPartMap, cartesianPhysicalConjugation_apply]

theorem toroidalPartMap_conjugate : operatorConjugation 3 1 toroidalPartMap = toroidalPartMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 1 (toroidalPartMap (cartesianPhysicalConjugation 3 vector)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [toroidalPartMap, cartesianPhysicalConjugation_apply]

theorem planarInclusionMap_conjugate : operatorConjugation 2 3 planarInclusionMap = planarInclusionMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 3 (planarInclusionMap (cartesianPhysicalConjugation 2 vector)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarInclusionMap, cartesianPhysicalConjugation_apply]

theorem toroidalInclusionMap_conjugate : operatorConjugation 1 3 toroidalInclusionMap = toroidalInclusionMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 3 (toroidalInclusionMap (cartesianPhysicalConjugation 1 vector)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [toroidalInclusionMap, cartesianPhysicalConjugation_apply]

theorem planarPartCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (planarPartCore parameters field) =
      planarPartCore parameters (cartesianCoreConjugation parameters field) := by
  rw [planarPartCore, valueMapCore_conjugate, planarPartMap_conjugate]

theorem toroidalPartCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (toroidalPartCore parameters field) =
      toroidalPartCore parameters (cartesianCoreConjugation parameters field) := by
  rw [toroidalPartCore, valueMapCore_conjugate, toroidalPartMap_conjugate]

theorem planarInclusionCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (planarInclusionCore parameters field) =
      planarInclusionCore parameters (cartesianCoreConjugation parameters field) := by
  rw [planarInclusionCore, valueMapCore_conjugate, planarInclusionMap_conjugate]

theorem toroidalInclusionCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 1) :
    cartesianCoreConjugation parameters (toroidalInclusionCore parameters field) =
      toroidalInclusionCore parameters (cartesianCoreConjugation parameters field) := by
  rw [toroidalInclusionCore, valueMapCore_conjugate, toroidalInclusionMap_conjugate]

theorem quarterValueMap_conjugate : operatorConjugation 2 2 quarterValueMap = quarterValueMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 2 (quarterValueMap (cartesianPhysicalConjugation 2 vector)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [quarterValueMap, quarterValueLinear,
      cartesianPhysicalConjugation_apply]

theorem reflectionValueMap_conjugate : operatorConjugation 2 2 reflectionValueMap = reflectionValueMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cartesianPhysicalConjugation 2 (reflectionValueMap (cartesianPhysicalConjugation 2 vector)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [reflectionValueMap, reflectionValueLinear,
      cartesianPhysicalConjugation_apply]

theorem positiveHelicity_conjugate : operatorConjugation 2 2 positiveHelicity = negativeHelicity := by
  rw [positiveHelicity, operatorConjugation_complex_smul, map_sub,
    operatorConjugation_id, operatorConjugation_complex_smul, quarterValueMap_conjugate]
  norm_num [negativeHelicity, map_div₀, map_ofNat]
  module

theorem negativeHelicity_conjugate : operatorConjugation 2 2 negativeHelicity = positiveHelicity := by
  rw [negativeHelicity, operatorConjugation_complex_smul, map_add,
    operatorConjugation_id, operatorConjugation_complex_smul, quarterValueMap_conjugate]
  norm_num [positiveHelicity, map_div₀, map_ofNat, sub_eq_add_neg]
  module

theorem equivariantAverageCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (equivariantAverageCore parameters field) =
      equivariantAverageCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
      (valueMapCore positiveHelicity parameters (angularCore parameters 1 field) +
        valueMapCore negativeHelicity parameters (angularCore parameters (-1) field)) = _
  rw [map_add, valueMapCore_conjugate, valueMapCore_conjugate,
    positiveHelicity_conjugate, negativeHelicity_conjugate, angularCore_conjugate, angularCore_conjugate]
  simp only [neg_neg]
  exact add_comm _ _

theorem reflectedVectorCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (reflectedVectorCore parameters field) =
      reflectedVectorCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (valueMapCore reflectionValueMap parameters (orthogonalCore parameters cartesianReflectionEquiv field)) = _
  rw [valueMapCore_conjugate, reflectionValueMap_conjugate, orthogonalCore_conjugate]
  rfl

theorem tangentialCore_conjugate (parameters : PhaseParameters) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (tangentialCore parameters field) =
      tangentialCore parameters (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters ((1 / 2 : ℂ) •
    (equivariantAverageCore parameters field -
      reflectedVectorCore parameters (equivariantAverageCore parameters field))) = _
  rw [coreConjugation_complex_smul, map_sub, reflectedVectorCore_conjugate,
    equivariantAverageCore_conjugate]
  norm_num [map_div₀, map_ofNat]
  rfl

end Grad.CompletedReality
