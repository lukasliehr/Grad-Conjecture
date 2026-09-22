import SCS12OriginalFlatInputs
import SCS11DecodedRowAlgebra
import SBT14PolarEndpointFormula

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarAngular Grad.SourceBoundaryTrace Grad.BoundaryTrace

theorem originalRowCoefficient_shift_zero {dimension : ℕ} (parameters : PhaseParameters)
    (lower radius : ℝ) (shift : ℤ) (field : DivisionRow dimension lower) (mode : ℤ × ℤ) :
    originalRowCoefficient parameters 0 lower (annularRowShift lower 0 shift field) radius mode =
      originalRowCoefficient parameters 0 lower field radius (mode.1 - shift, mode.2) := by
  unfold originalRowCoefficient
  simp only [annularRowShift_apply, annularShiftScalar, pow_zero, Complex.ofReal_one, one_smul]
  rfl

theorem originalRowCoefficient_valueMap_ae {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : DivisionRow sourceDimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters power lower (divisionRowValueMap lower mapping field) radius mode =
        mapping (originalRowCoefficient parameters power lower field radius mode) := by
  apply ae_all_iff.mpr
  intro mode
  filter_upwards [mapping.coeFn_compLpL (field mode)] with radius same
  unfold originalRowCoefficient
  change _ • (mapping.compLpL 2 (volume.restrict (Icc lower 1)) (field mode)) radius = _
  rw [same, map_smul]

theorem originalRowCoefficient_cosine_zero_ae {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters 0 lower (cosineRow lower 0 field) radius mode =
        (2 : ℂ)⁻¹ • (originalRowCoefficient parameters 0 lower field radius (mode.1 - 1, mode.2) +
          originalRowCoefficient parameters 0 lower field radius (mode.1 + 1, mode.2)) := by
  filter_upwards [originalRowCoefficient_smul_ae parameters 0 lower (2 : ℂ)⁻¹
      (annularRowShift lower 0 1 field + annularRowShift lower 0 (-1) field),
    originalRowCoefficient_add_ae parameters 0 lower
      (annularRowShift lower 0 1 field) (annularRowShift lower 0 (-1) field)] with radius scalar add
  intro mode
  rw [cosineRow, scalar, add, originalRowCoefficient_shift_zero, originalRowCoefficient_shift_zero]
  simp only [sub_neg_eq_add]

theorem originalRowCoefficient_sine_zero_ae {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters 0 lower (sineRow lower 0 field) radius mode =
        (2 * Complex.I : ℂ)⁻¹ • (originalRowCoefficient parameters 0 lower field radius (mode.1 - 1, mode.2) -
          originalRowCoefficient parameters 0 lower field radius (mode.1 + 1, mode.2)) := by
  filter_upwards [originalRowCoefficient_smul_ae parameters 0 lower (2 * Complex.I : ℂ)⁻¹
      (annularRowShift lower 0 1 field - annularRowShift lower 0 (-1) field),
    originalRowCoefficient_sub_ae parameters 0 lower
      (annularRowShift lower 0 1 field) (annularRowShift lower 0 (-1) field)] with radius scalar sub
  intro mode
  rw [sineRow, scalar, sub, originalRowCoefficient_shift_zero, originalRowCoefficient_shift_zero]
  simp only [sub_neg_eq_add]

end Grad.SourceCollarFullSource
