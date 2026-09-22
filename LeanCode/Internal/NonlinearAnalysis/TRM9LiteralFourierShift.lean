import TRM8LiteralCoreFormula

noncomputable section

open Set MeasureTheory

namespace Grad.SourceCollarAngular

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace
open Grad.SourceCollarDivision

theorem cellExponential_mul (first second : ℤ) (angle : ℝ) :
    cellExponential first angle * cellExponential second angle =
      cellExponential (first + second) angle := by
  unfold cellExponential
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem angularCoefficient_character_mul {dimension : ℕ}
    (field : ℝ → ComplexEuclidean dimension) (shift mode : ℤ) :
    angularCoefficient (fun angle => cellExponential shift angle • field angle) mode =
      angularCoefficient field (mode - shift) := by
  rw [angularCoefficient_compact, angularCoefficient_compact]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [smul_smul, cellExponential_mul]
  congr 2
  ring

theorem cellExponential_one (angle : ℝ) :
    cellExponential 1 angle =
      (Real.cos angle : ℂ) + (Real.sin angle : ℂ) * Complex.I := by
  unfold cellExponential
  norm_num only [Int.cast_one, mul_one]
  rw [show Complex.I * (angle : ℂ) = (angle : ℂ) * Complex.I by ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem cellExponential_neg_one (angle : ℝ) :
    cellExponential (-1) angle =
      (Real.cos angle : ℂ) - (Real.sin angle : ℂ) * Complex.I := by
  unfold cellExponential
  rw [show Complex.I * ((-1 : ℤ) : ℂ) * (angle : ℂ) =
      (((-1 : ℝ) * angle : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  norm_num [Real.cos_neg, Real.sin_neg]
  simp only [sub_eq_add_neg]

theorem complex_cos_character (angle : ℝ) :
    (Real.cos angle : ℂ) = (2 : ℂ)⁻¹ *
      (cellExponential 1 angle + cellExponential (-1) angle) := by
  rw [cellExponential_one, cellExponential_neg_one]
  norm_num
  ring

theorem complex_sin_character (angle : ℝ) :
    (Real.sin angle : ℂ) = (2 * Complex.I : ℂ)⁻¹ *
      (cellExponential 1 angle - cellExponential (-1) angle) := by
  rw [cellExponential_one, cellExponential_neg_one]
  have imaginaryNonzero : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

/-- Literal Fourier formula for multiplication by `cos θ`. -/
theorem angularCoefficient_cos_mul {dimension : ℕ}
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field)
    (mode : ℤ) :
    angularCoefficient (fun angle => (Real.cos angle : ℂ) • field angle) mode =
      (2 : ℂ)⁻¹ •
        (angularCoefficient field (mode - 1) + angularCoefficient field (mode + 1)) := by
  let positiveField : ℝ → ComplexEuclidean dimension :=
    fun angle => cellExponential 1 angle • field angle
  let negativeField : ℝ → ComplexEuclidean dimension :=
    fun angle => cellExponential (-1) angle • field angle
  have positiveContinuous : Continuous positiveField :=
    ((cellExponential_smooth 1).continuous).smul continuousField
  have negativeContinuous : Continuous negativeField :=
    ((cellExponential_smooth (-1)).continuous).smul continuousField
  have expression : (fun angle => (Real.cos angle : ℂ) • field angle) =
      (2 : ℂ)⁻¹ • (positiveField + negativeField) := by
    funext angle
    simp only [Pi.smul_apply, Pi.add_apply, positiveField, negativeField,
      ← add_smul, smul_smul]
    rw [← complex_cos_character]
  rw [expression, angularCoefficient_smul_continuous,
    angularCoefficient_add_continuous positiveField negativeField
      positiveContinuous negativeContinuous,
    angularCoefficient_character_mul, angularCoefficient_character_mul]
  congr 2

/-- Literal Fourier formula for multiplication by `sin θ`. -/
theorem angularCoefficient_sin_mul {dimension : ℕ}
    (field : ℝ → ComplexEuclidean dimension) (continuousField : Continuous field)
    (mode : ℤ) :
    angularCoefficient (fun angle => (Real.sin angle : ℂ) • field angle) mode =
      (2 * Complex.I : ℂ)⁻¹ •
        (angularCoefficient field (mode - 1) - angularCoefficient field (mode + 1)) := by
  let positiveField : ℝ → ComplexEuclidean dimension :=
    fun angle => cellExponential 1 angle • field angle
  let negativeField : ℝ → ComplexEuclidean dimension :=
    fun angle => cellExponential (-1) angle • field angle
  have positiveContinuous : Continuous positiveField :=
    ((cellExponential_smooth 1).continuous).smul continuousField
  have negativeContinuous : Continuous negativeField :=
    ((cellExponential_smooth (-1)).continuous).smul continuousField
  have expression : (fun angle => (Real.sin angle : ℂ) • field angle) =
      (2 * Complex.I : ℂ)⁻¹ • (positiveField - negativeField) := by
    funext angle
    simp only [Pi.smul_apply, Pi.sub_apply, positiveField, negativeField,
      ← sub_smul, smul_smul]
    rw [← complex_sin_character]
  rw [expression, angularCoefficient_smul_continuous]
  rw [sub_eq_add_neg,
    angularCoefficient_add_continuous positiveField (-negativeField)
      positiveContinuous negativeContinuous.neg]
  have negField : -negativeField = (-1 : ℂ) • negativeField := by
    funext angle
    simp
  rw [negField]
  rw [angularCoefficient_smul_continuous,
    angularCoefficient_character_mul, angularCoefficient_character_mul]
  simp only [neg_one_smul]
  congr 2

end Grad.SourceCollarAngular
