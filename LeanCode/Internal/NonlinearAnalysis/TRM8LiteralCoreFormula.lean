import TRM7PolarContractions
import RSC13PublicRestriction

noncomputable section

namespace Grad.SourceCollarAngular

open Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.ClosedJets Grad.CartesianState Grad.Constraints.Gauges

theorem annularShiftScalar_mul_weight (power : ℕ) (shift : ℤ) (mode : ℤ × ℤ) :
    annularShiftScalar power shift mode *
        (annularFrequency (mode.1 - shift) mode.2 : ℂ) ^ power =
      (annularFrequency mode.1 mode.2 : ℂ) ^ power := by
  have denominator : annularFrequency (mode.1 - shift) mode.2 ≠ 0 :=
    ne_of_gt (annularFrequency_pos _ _)
  have denominatorComplex : (annularFrequency (mode.1 - shift) mode.2 : ℂ) ≠ 0 := by
    exact_mod_cast denominator
  unfold annularShiftScalar
  push_cast
  rw [div_pow]
  exact div_mul_cancel₀ _
    (pow_ne_zero _ denominatorComplex)

/-- The ratio in `annularRowShift` precisely changes the stored source
weight to the target weight; this is not an equivalent renorming. -/
theorem annularRowShift_weighted_coordinate {dimension : ℕ}
    (lower : ℝ) (power : ℕ) (shift : ℤ)
    (field : DivisionRow dimension lower) (mode : ℤ × ℤ)
    (raw : RadialL2 dimension lower)
    (source : field (mode.1 - shift, mode.2) =
      (annularFrequency (mode.1 - shift) mode.2 : ℂ) ^ power • raw) :
    annularRowShift lower power shift field mode =
      (annularFrequency mode.1 mode.2 : ℂ) ^ power • raw := by
  rw [annularRowShift_apply, source, smul_smul, annularShiftScalar_mul_weight]

/-- Exact shifted weighted Fourier-row formula for the radial polar
contraction, on every weak radial derivative coordinate of the accepted
restriction core. -/
theorem annularRadialContraction_restriction_core
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : GradeCore parameters 2 (power + radial))
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularRadialContraction lower positive power
      (completedRestriction lower positive bounded parameters power radial
        (aGradeEta parameters field))).val index mode =
      radialValueMap lower (planarComponentMap 0)
        ((2 : ℂ)⁻¹ •
          (annularShiftScalar power 1 mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 - 1, mode.2) +
            annularShiftScalar power (-1) mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 + 1, mode.2))) +
      radialValueMap lower (planarComponentMap 1)
        ((2 * Complex.I : ℂ)⁻¹ •
          (annularShiftScalar power 1 mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 - 1, mode.2) -
            annularShiftScalar power (-1) mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 + 1, mode.2))) := by
  rw [annularRadialContraction_apply, annularCosine_apply, annularSine_apply]
  simp only [completedRestriction_core, sub_neg_eq_add]

/-- Exact shifted weighted Fourier-row formula for the tangential polar
contraction, again including every radial graph coordinate. -/
theorem annularTangentialContraction_restriction_core
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : GradeCore parameters 2 (power + radial))
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularTangentialContraction lower positive power
      (completedRestriction lower positive bounded parameters power radial
        (aGradeEta parameters field))).val index mode =
      radialValueMap lower (planarComponentMap 1)
        ((2 : ℂ)⁻¹ •
          (annularShiftScalar power 1 mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 - 1, mode.2) +
            annularShiftScalar power (-1) mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 + 1, mode.2))) -
      radialValueMap lower (planarComponentMap 0)
        ((2 * Complex.I : ℂ)⁻¹ •
          (annularShiftScalar power 1 mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 - 1, mode.2) -
            annularShiftScalar power (-1) mode •
              restrictionModeLp lower power index.val parameters field.toCore
                (mode.1 + 1, mode.2))) := by
  rw [annularTangentialContraction_apply, annularCosine_apply, annularSine_apply]
  simp only [completedRestriction_core, sub_neg_eq_add]

end Grad.SourceCollarAngular
