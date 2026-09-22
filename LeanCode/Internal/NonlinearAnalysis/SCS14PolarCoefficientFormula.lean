import SCS13DecodedPolarRows

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarAngular Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.Constraints.Gauges

def radialPolarField (field : ℝ → ComplexEuclidean 2) (angle : ℝ) : ComplexEuclidean 1 :=
  planarComponentMap 0 ((Real.cos angle : ℂ) • field angle) +
    planarComponentMap 1 ((Real.sin angle : ℂ) • field angle)

def tangentialPolarField (field : ℝ → ComplexEuclidean 2) (angle : ℝ) : ComplexEuclidean 1 :=
  planarComponentMap 1 ((Real.cos angle : ℂ) • field angle) -
    planarComponentMap 0 ((Real.sin angle : ℂ) • field angle)

theorem radialPolarField_coefficient (field : ℝ → ComplexEuclidean 2)
    (continuousField : Continuous field) (mode : ℤ) :
    angularCoefficient (radialPolarField field) mode =
      planarComponentMap 0 ((2 : ℂ)⁻¹ •
        (angularCoefficient field (mode - 1) + angularCoefficient field (mode + 1))) +
      planarComponentMap 1 ((2 * Complex.I : ℂ)⁻¹ •
        (angularCoefficient field (mode - 1) - angularCoefficient field (mode + 1))) := by
  have cosine : Continuous (fun angle => (Real.cos angle : ℂ) • field angle) :=
    (Complex.continuous_ofReal.comp Real.continuous_cos).smul continuousField
  have sine : Continuous (fun angle => (Real.sin angle : ℂ) • field angle) :=
    (Complex.continuous_ofReal.comp Real.continuous_sin).smul continuousField
  change angularCoefficient ((fun angle => planarComponentMap 0 ((Real.cos angle : ℂ) • field angle)) +
    (fun angle => planarComponentMap 1 ((Real.sin angle : ℂ) • field angle))) mode = _
  rw [angularCoefficient_add_continuous
    (fun angle => planarComponentMap 0 ((Real.cos angle : ℂ) • field angle))
    (fun angle => planarComponentMap 1 ((Real.sin angle : ℂ) • field angle))
    ((planarComponentMap 0).continuous.comp cosine) ((planarComponentMap 1).continuous.comp sine),
    angularCoefficient_valueMap _ _ cosine, angularCoefficient_valueMap _ _ sine,
    angularCoefficient_cos_mul _ continuousField, angularCoefficient_sin_mul _ continuousField]

theorem tangentialPolarField_coefficient (field : ℝ → ComplexEuclidean 2)
    (continuousField : Continuous field) (mode : ℤ) :
    angularCoefficient (tangentialPolarField field) mode =
      planarComponentMap 1 ((2 : ℂ)⁻¹ •
        (angularCoefficient field (mode - 1) + angularCoefficient field (mode + 1))) -
      planarComponentMap 0 ((2 * Complex.I : ℂ)⁻¹ •
        (angularCoefficient field (mode - 1) - angularCoefficient field (mode + 1))) := by
  have cosine : Continuous (fun angle => (Real.cos angle : ℂ) • field angle) :=
    (Complex.continuous_ofReal.comp Real.continuous_cos).smul continuousField
  have sine : Continuous (fun angle => (Real.sin angle : ℂ) • field angle) :=
    (Complex.continuous_ofReal.comp Real.continuous_sin).smul continuousField
  change angularCoefficient ((fun angle => planarComponentMap 1 ((Real.cos angle : ℂ) • field angle)) -
    (fun angle => planarComponentMap 0 ((Real.sin angle : ℂ) • field angle))) mode = _
  rw [angularCoefficient_sub_continuous
    (fun angle => planarComponentMap 1 ((Real.cos angle : ℂ) • field angle))
    (fun angle => planarComponentMap 0 ((Real.sin angle : ℂ) • field angle))
    ((planarComponentMap 1).continuous.comp cosine) ((planarComponentMap 0).continuous.comp sine),
    angularCoefficient_valueMap _ _ cosine, angularCoefficient_valueMap _ _ sine,
    angularCoefficient_cos_mul _ continuousField, angularCoefficient_sin_mul _ continuousField]

theorem radialRowContraction_decoded_ae (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow 2 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters 0 lower (radialRowContraction lower positive 0 field) radius mode =
      planarComponentMap 0 ((2 : ℂ)⁻¹ •
        (originalRowCoefficient parameters 0 lower field radius (mode.1 - 1, mode.2) +
          originalRowCoefficient parameters 0 lower field radius (mode.1 + 1, mode.2))) +
      planarComponentMap 1 ((2 * Complex.I : ℂ)⁻¹ •
        (originalRowCoefficient parameters 0 lower field radius (mode.1 - 1, mode.2) -
          originalRowCoefficient parameters 0 lower field radius (mode.1 + 1, mode.2))) := by
  filter_upwards [originalRowCoefficient_add_ae parameters 0 lower
      (divisionRowValueMap lower (planarComponentMap 0) (cosineRow lower 0 field))
      (divisionRowValueMap lower (planarComponentMap 1) (sineRow lower 0 field)),
    originalRowCoefficient_valueMap_ae parameters 0 lower (planarComponentMap 0) (cosineRow lower 0 field),
    originalRowCoefficient_valueMap_ae parameters 0 lower (planarComponentMap 1) (sineRow lower 0 field),
    originalRowCoefficient_cosine_zero_ae parameters lower field,
    originalRowCoefficient_sine_zero_ae parameters lower field] with radius add first second cosine sine
  intro mode
  rw [radialRowContraction_formula, add, first, second, cosine, sine]

theorem tangentialRowContraction_decoded_ae (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow 2 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      originalRowCoefficient parameters 0 lower (tangentialRowContraction lower positive 0 field) radius mode =
      planarComponentMap 1 ((2 : ℂ)⁻¹ •
        (originalRowCoefficient parameters 0 lower field radius (mode.1 - 1, mode.2) +
          originalRowCoefficient parameters 0 lower field radius (mode.1 + 1, mode.2))) -
      planarComponentMap 0 ((2 * Complex.I : ℂ)⁻¹ •
        (originalRowCoefficient parameters 0 lower field radius (mode.1 - 1, mode.2) -
          originalRowCoefficient parameters 0 lower field radius (mode.1 + 1, mode.2))) := by
  filter_upwards [originalRowCoefficient_sub_ae parameters 0 lower
      (divisionRowValueMap lower (planarComponentMap 1) (cosineRow lower 0 field))
      (divisionRowValueMap lower (planarComponentMap 0) (sineRow lower 0 field)),
    originalRowCoefficient_valueMap_ae parameters 0 lower (planarComponentMap 1) (cosineRow lower 0 field),
    originalRowCoefficient_valueMap_ae parameters 0 lower (planarComponentMap 0) (sineRow lower 0 field),
    originalRowCoefficient_cosine_zero_ae parameters lower field,
    originalRowCoefficient_sine_zero_ae parameters lower field] with radius sub first second cosine sine
  intro mode
  rw [tangentialRowContraction_formula, sub, first, second, cosine, sine]

end Grad.SourceCollarFullSource
