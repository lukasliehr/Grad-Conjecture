import ValueMapGrade
import AngularCharacters

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.Constraints

open Grad.ClosedJets

def quarterValueLinear : ComplexEuclidean 2 →ₗ[ℂ] ComplexEuclidean 2 where
  toFun value := WithLp.toLp 2 ![-value 1, value 0]
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp
    ring
  map_smul' scalar value := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp

theorem quarterValue_norm (value : ComplexEuclidean 2) : ‖quarterValueLinear value‖ = ‖value‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [Fin.sum_univ_two]
  change Real.sqrt (‖-value 1‖ ^ 2 + ‖value 0‖ ^ 2) = _
  rw [norm_neg, add_comm]

def quarterValueMap : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  quarterValueLinear.mkContinuous 1 (fun value => by rw [quarterValue_norm, one_mul])

def reflectionValueLinear : ComplexEuclidean 2 →ₗ[ℂ] ComplexEuclidean 2 where
  toFun value := WithLp.toLp 2 ![value 0, -value 1]
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp
    ring
  map_smul' scalar value := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp

theorem reflectionValue_norm (value : ComplexEuclidean 2) :
    ‖reflectionValueLinear value‖ = ‖value‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [Fin.sum_univ_two]
  change Real.sqrt (‖value 0‖ ^ 2 + ‖-value 1‖ ^ 2) = _
  rw [norm_neg]

def reflectionValueMap : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  reflectionValueLinear.mkContinuous 1 (fun value => by rw [reflectionValue_norm, one_mul])

def rotationValueMap (angle : ℝ) : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (Real.cos angle : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2) +
    (Real.sin angle : ℂ) • quarterValueMap

def positiveHelicity : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ (ComplexEuclidean 2) - Complex.I • quarterValueMap)

def negativeHelicity : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ (ComplexEuclidean 2) + Complex.I • quarterValueMap)

theorem quarterValueMap_square (value : ComplexEuclidean 2) :
    quarterValueMap (quarterValueMap value) = -value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [quarterValueMap, quarterValueLinear]

theorem reflectionValueMap_square (value : ComplexEuclidean 2) :
    reflectionValueMap (reflectionValueMap value) = value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [reflectionValueMap, reflectionValueLinear]

theorem angularCharacter_trig (mode : ℤ) (angle : ℝ) :
    angularCharacter mode angle =
      (Real.cos ((-mode : ℝ) * angle) : ℂ) +
        (Real.sin ((-mode : ℝ) * angle) : ℂ) * Complex.I := by
  unfold angularCharacter Grad.CartesianState.cellExponential
  rw [show Complex.I * ((-mode : ℤ) : ℂ) * (angle : ℂ) =
      (((-mode : ℝ) * angle : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem positiveHelicity_apply (value : ComplexEuclidean 2) :
    positiveHelicity value = WithLp.toLp 2
      ![(value 0 + Complex.I * value 1) / 2, (value 1 - Complex.I * value 0) / 2] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [positiveHelicity, quarterValueMap, quarterValueLinear] <;> ring

theorem negativeHelicity_apply (value : ComplexEuclidean 2) :
    negativeHelicity value = WithLp.toLp 2
      ![(value 0 - Complex.I * value 1) / 2, (value 1 + Complex.I * value 0) / 2] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [negativeHelicity, quarterValueMap, quarterValueLinear] <;> ring

theorem rotationValueMap_apply (angle : ℝ) (value : ComplexEuclidean 2) :
    rotationValueMap angle value = WithLp.toLp 2
      ![(Real.cos angle : ℂ) * value 0 - (Real.sin angle : ℂ) * value 1,
        (Real.sin angle : ℂ) * value 0 + (Real.cos angle : ℂ) * value 1] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [rotationValueMap, quarterValueMap, quarterValueLinear] <;> ring

theorem rotationValueMap_character (angle : ℝ) (value : ComplexEuclidean 2) :
    rotationValueMap (-angle) value =
      angularCharacter 1 angle • positiveHelicity value +
        angularCharacter (-1) angle • negativeHelicity value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [rotationValueMap_apply, positiveHelicity_apply, negativeHelicity_apply,
      angularCharacter_trig] <;> ring_nf <;> simp [Complex.I_sq]

end Grad.Constraints
