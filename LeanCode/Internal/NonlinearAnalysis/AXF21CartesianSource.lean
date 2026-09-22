import AXF20VectorNorm

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

open scoped BigOperators

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection
open Grad.NonlinearProduct

variable {parameters : PhaseParameters}

def componentInsertion (index : Fin 2) : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 2 :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).smulRight
    (EuclideanSpace.single index 1)

def vectorTuple (first second : ACore parameters 1) : ACore parameters 2 :=
  Grad.Constraints.valueMapCore (componentInsertion 0) parameters first +
    Grad.Constraints.valueMapCore (componentInsertion 1) parameters second

theorem vectorTuple_value (first second : ACore parameters 1) (cell : ℤ) (point : ClosedDisk) :
    ((vectorTuple first second).val cell).value point =
      WithLp.toLp 2 ![(first.val cell).value point 0, (second.val cell).value point 0] := by
  apply PiLp.ext
  intro index
  change (valueMapJet (componentInsertion 0) (first.val cell)).value point index +
    (valueMapJet (componentInsertion 1) (second.val cell)).value point index = _
  rw [valueMapJet_value, valueMapJet_value]
  fin_cases index <;> simp [componentInsertion]

theorem componentCore_vectorTuple (first second : ACore parameters 1) (index : Fin 2) :
    componentCore 2 index (vectorTuple first second) = ![first, second] index := by
  apply Grad.NonlinearQuotientBounds.acore_ext
  intro cell point
  apply PiLp.ext
  intro component
  fin_cases component
  change (valueMapJet (componentValue 2 index) ((vectorTuple first second).val cell)).value point 0 = _
  rw [valueMapJet_value, componentValue_apply, vectorTuple_value]
  fin_cases index <;> rfl

theorem vectorTuple_components (field : ACore parameters 2) :
    vectorTuple (componentCore 2 0 field) (componentCore 2 1 field) = field := by
  apply Grad.NonlinearQuotientBounds.acore_ext
  intro cell point
  rw [vectorTuple_value]
  apply PiLp.ext
  intro index
  fin_cases index <;>
    change (valueMapJet (componentValue 2 _) (field.val cell)).value point 0 = _ <;>
    rw [valueMapJet_value, componentValue_apply] <;> rfl

theorem vectorTuple_original_norm (grade : ℕ) (first second : ACore parameters 1) :
    originalGradeNorm grade (vectorTuple first second) ^ 2 =
      originalGradeNorm grade first ^ 2 + originalGradeNorm grade second ^ 2 := by
  rw [originalGradeNorm_components, Fin.sum_univ_two,
    componentCore_vectorTuple, componentCore_vectorTuple]
  rfl

def cartesianSourceVector (source : SmoothQuotient parameters) : ACore parameters 2 :=
  vectorTuple (cartesianSpinFirst source) (cartesianSpinSecond source)

/-- Literal BS2/BS3 in the original vector-valued A^q norm. -/
theorem originalSpin_cartesian_vector_norm (parameters : PhaseParameters)
    (grade : ℕ) (source : SmoothQuotient parameters) :
    quotientNorm parameters grade source ^ 2 =
      2 * originalGradeNorm grade (cartesianSourceVector source) ^ 2 +
        originalGradeNorm grade (source 2) ^ 2 + originalGradeNorm grade (source 3) ^ 2 := by
  rw [cartesianSourceVector, vectorTuple_original_norm]
  exact originalSpin_cartesian_components_norm parameters grade source

theorem cartesianSourceVector_literal (source : SmoothQuotient parameters)
    (cell : ℤ) (point : ClosedDisk) :
    ((cartesianSourceVector source).val cell).value point = WithLp.toLp 2
      ![(((source 0).val cell).value point 0 + ((source 1).val cell).value point 0) / 2,
        (((source 0).val cell).value point 0 - ((source 1).val cell).value point 0) /
          (2 * Complex.I)] := by
  rw [cartesianSourceVector, vectorTuple_value]
  apply PiLp.ext
  intro index
  change ![((cartesianSpinFirst source).val cell).value point 0,
    ((cartesianSpinSecond source).val cell).value point 0] index = _
  fin_cases index
  · change (1 / 2 : ℂ) * (((source 0).val cell).value point 0 +
      ((source 1).val cell).value point 0) =
        (((source 0).val cell).value point 0 + ((source 1).val cell).value point 0) / 2
    ring
  · simp only [cartesianSpinSecond, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.proj_apply]
    change (-Complex.I / 2) * (((source 0).val cell).value point 0 +
      (-1) * ((source 1).val cell).value point 0) =
        (((source 0).val cell).value point 0 - ((source 1).val cell).value point 0) / (2 * Complex.I)
    have inverse : (2 * Complex.I)⁻¹ = -Complex.I / 2 := by
      apply inv_eq_of_mul_eq_one_right
      calc _ = -(Complex.I * Complex.I) := by ring
           _ = 1 := by rw [Complex.I_mul_I]; norm_num
    simp only [div_eq_mul_inv, inverse]
    ring

end Grad.FlatSourceProjection
