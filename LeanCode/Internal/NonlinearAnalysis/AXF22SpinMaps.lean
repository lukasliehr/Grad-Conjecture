import AXF21CartesianSource

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection

variable {parameters : PhaseParameters}

def spinValue (sign : ℂ) : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 1 :=
  componentValue 2 0 + (sign * Complex.I) • componentValue 2 1

@[simp] theorem spinValue_apply (sign : ℂ) (value : ComplexEuclidean 2) :
    spinValue sign value 0 = value 0 + sign * Complex.I * value 1 := by
  simp [spinValue]

def spinCore (sign : ℂ) : ACore parameters 2 →ₗ[ℂ] ACore parameters 1 :=
  Grad.Constraints.valueMapCore (spinValue sign) parameters

theorem spinCore_components (sign : ℂ) (field : ACore parameters 2) :
    spinCore sign field = componentCore 2 0 field +
      (sign * Complex.I) • componentCore 2 1 field := by
  apply Grad.NonlinearQuotientBounds.acore_ext
  intro cell point
  apply PiLp.ext
  intro component
  fin_cases component
  change (valueMapJet (spinValue sign) (field.val cell)).value point 0 =
    (valueMapJet (componentValue 2 0) (field.val cell)).value point 0 +
      (sign * Complex.I) * (valueMapJet (componentValue 2 1) (field.val cell)).value point 0
  simp only [valueMapJet_value, spinValue_apply, componentValue_apply]

theorem spinCore_cartesianSource_plus (source : SmoothQuotient parameters) :
    spinCore 1 (cartesianSourceVector source) = source 0 := by
  rw [spinCore_components, cartesianSourceVector,
    componentCore_vectorTuple, componentCore_vectorTuple]
  simp only [one_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact cartesianSpin_reconstruct_zero source

theorem spinCore_cartesianSource_minus (source : SmoothQuotient parameters) :
    spinCore (-1) (cartesianSourceVector source) = source 1 := by
  rw [spinCore_components, cartesianSourceVector,
    componentCore_vectorTuple, componentCore_vectorTuple]
  simp only [neg_one_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc _ = cartesianSpinFirst source - Complex.I • cartesianSpinSecond source := by module
       _ = source 1 := cartesianSpin_reconstruct_one source

theorem coreValueMap_comp {first second third : ℕ}
    (outer : ComplexEuclidean second →L[ℂ] ComplexEuclidean third)
    (inner : ComplexEuclidean first →L[ℂ] ComplexEuclidean second)
    (field : ACore parameters first) :
    Grad.Constraints.valueMapCore outer parameters
      (Grad.Constraints.valueMapCore inner parameters field) =
    Grad.Constraints.valueMapCore (outer.comp inner) parameters field := by
  apply Subtype.ext
  funext cell
  exact valueMapJet_comp inner outer (field.val cell)

theorem coreValueMap_zero {first second : ℕ} (field : ACore parameters first) :
    Grad.Constraints.valueMapCore (0 : ComplexEuclidean first →L[ℂ] ComplexEuclidean second)
      parameters field = 0 := by
  apply Subtype.ext
  funext cell
  exact valueMapJet_zero (field.val cell)

theorem spinCore_angular (sign : ℂ) (mode : ℤ) (field : ACore parameters 2) :
    spinCore sign (angularCore parameters mode field) =
      angularCore parameters mode (spinCore sign field) := by
  apply Subtype.ext
  funext cell
  exact (angularClosedJet_valueMap (spinValue sign) mode (field.val cell)).symm

theorem spinValue_positive : (spinValue 1).comp positiveHelicity = spinValue 1 := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  fin_cases component
  simp [ContinuousLinearMap.comp_apply, spinValue_apply, positiveHelicity_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem spinValue_positive_zero : (spinValue (-1)).comp positiveHelicity = 0 := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  fin_cases component
  simp [ContinuousLinearMap.comp_apply, spinValue_apply, positiveHelicity_apply]
  ring_nf
  simp [Complex.I_sq]

theorem spinValue_negative : (spinValue (-1)).comp negativeHelicity = spinValue (-1) := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  fin_cases component
  simp [ContinuousLinearMap.comp_apply, spinValue_apply, negativeHelicity_apply]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem spinValue_negative_zero : (spinValue 1).comp negativeHelicity = 0 := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro component
  fin_cases component
  simp [ContinuousLinearMap.comp_apply, spinValue_apply, negativeHelicity_apply]
  ring_nf
  simp [Complex.I_sq]

theorem spinCore_equivariant_plus (field : ACore parameters 2) :
    spinCore 1 (equivariantAverageCore parameters field) =
      angularCore parameters 1 (spinCore 1 field) := by
  change spinCore 1 (Grad.Constraints.valueMapCore positiveHelicity parameters
    (angularCore parameters 1 field) + Grad.Constraints.valueMapCore negativeHelicity parameters
    (angularCore parameters (-1) field)) = _
  rw [map_add]
  change Grad.Constraints.valueMapCore (spinValue 1) parameters _ +
    Grad.Constraints.valueMapCore (spinValue 1) parameters _ = _
  rw [coreValueMap_comp, coreValueMap_comp, spinValue_positive, spinValue_negative_zero,
    coreValueMap_zero, add_zero]
  exact spinCore_angular 1 1 field

theorem spinCore_equivariant_minus (field : ACore parameters 2) :
    spinCore (-1) (equivariantAverageCore parameters field) =
      angularCore parameters (-1) (spinCore (-1) field) := by
  change spinCore (-1) (Grad.Constraints.valueMapCore positiveHelicity parameters
    (angularCore parameters 1 field) + Grad.Constraints.valueMapCore negativeHelicity parameters
    (angularCore parameters (-1) field)) = _
  rw [map_add]
  change Grad.Constraints.valueMapCore (spinValue (-1)) parameters _ +
    Grad.Constraints.valueMapCore (spinValue (-1)) parameters _ = _
  rw [coreValueMap_comp, coreValueMap_comp, spinValue_positive_zero, spinValue_negative,
    coreValueMap_zero, zero_add]
  exact spinCore_angular (-1) (-1) field

end Grad.FlatSourceProjection
