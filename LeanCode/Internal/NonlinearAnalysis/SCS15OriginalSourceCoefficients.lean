import SCS14PolarCoefficientFormula

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarAngular Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.SourceCollarBulk Grad.AxisCore

def originalDividedCell {dimension grade : ℕ} (parameters : PhaseParameters) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) (cell : ℤ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angle : ℝ) : ComplexEuclidean dimension :=
  radius⁻¹ • completedOriginalCell parameters large cell field (polarClosedPoint radius angle nonnegative bounded)

theorem originalDividedCell_continuous {dimension grade : ℕ} (parameters : PhaseParameters) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) (cell : ℤ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Continuous (originalDividedCell parameters large field cell radius nonnegative bounded) := by
  have pointContinuous : Continuous (fun angle => polarClosedPoint radius angle nonnegative bounded) :=
    (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  exact (continuous_const : Continuous (fun _ : ℝ => radius⁻¹)).smul
    ((completedOriginalCell parameters large cell field).continuous.comp pointContinuous)

/-- Actual original polar source cells, divided by the physical radius. -/
def originalDividedSourceCells {grade : ℕ} (parameters : PhaseParameters) (L : ℝ) (large : 3 ≤ grade)
    (source : ZAmbient parameters grade) (cell : ℤ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) : Fin 3 → ℝ → ComplexEuclidean 1 :=
  ![radialPolarField (originalDividedCell parameters large (originalSourcePlanar parameters grade source)
      cell radius nonnegative bounded),
    tangentialPolarField (originalDividedCell parameters large (originalSourcePlanar parameters grade source)
      cell radius nonnegative bounded),
    (L : ℂ)⁻¹ • originalDividedCell parameters large (source 3) cell radius nonnegative bounded]

theorem dividedSourceRows_original_zero {grade : ℕ}
    (parameters : PhaseParameters) (L : ℝ) (large : 3 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (source : ZAmbient parameters grade)
    (planarFlat : OriginalValueFlat parameters large (originalSourcePlanar parameters grade source))
    (fourthFlat : OriginalValueFlat parameters large (source 3)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      ∀ (component : Fin 3) (mode : ℤ × ℤ),
        originalRowCoefficient parameters 0 lower
          (dividedSourceRows (power := 0) lower positive bounded parameters L (by omega) source component) radius mode =
        angularCoefficient (originalDividedSourceCells parameters L large source mode.2 radius
          (positive.le.trans inside.1) inside.2 component) mode.1 := by
  have planar := ae_all_iff.mpr (fun mode : ℤ × ℤ =>
    dividedRow_original_coefficient (power := 0) lower positive bounded parameters (by omega)
      (originalSourcePlanar parameters grade source) planarFlat mode)
  have fourth := ae_all_iff.mpr (fun mode : ℤ × ℤ =>
    dividedRow_original_coefficient (power := 0) lower positive bounded parameters (by omega)
      (source 3) fourthFlat mode)
  filter_upwards [planar, fourth,
    radialRowContraction_decoded_ae parameters lower positive (dividedPlanar lower positive bounded parameters (by omega) source),
    tangentialRowContraction_decoded_ae parameters lower positive (dividedPlanar lower positive bounded parameters (by omega) source),
    originalRowCoefficient_smul_ae parameters 0 lower (L : ℂ)⁻¹
      (completedDivisionRow (power := 0) (radial := 0) lower positive bounded parameters (by omega) (source 3))]
    with radius planar fourth radial tangential scalar
  intro inside component mode
  have continuousPlanar := originalDividedCell_continuous parameters large
    (originalSourcePlanar parameters grade source) mode.2 radius (positive.le.trans inside.1) inside.2
  fin_cases component
  · change originalRowCoefficient parameters 0 lower
      (radialRowContraction lower positive 0 (dividedPlanar lower positive bounded parameters (by omega) source)) radius mode =
        angularCoefficient (radialPolarField (originalDividedCell parameters large
          (originalSourcePlanar parameters grade source) mode.2 radius (positive.le.trans inside.1) inside.2)) mode.1
    rw [radial, radialPolarField_coefficient _ continuousPlanar]
    simp only [dividedPlanar, planar _ inside]
    rfl
  · change originalRowCoefficient parameters 0 lower
      (tangentialRowContraction lower positive 0 (dividedPlanar lower positive bounded parameters (by omega) source)) radius mode =
        angularCoefficient (tangentialPolarField (originalDividedCell parameters large
          (originalSourcePlanar parameters grade source) mode.2 radius (positive.le.trans inside.1) inside.2)) mode.1
    rw [tangential, tangentialPolarField_coefficient _ continuousPlanar]
    simp only [dividedPlanar, planar _ inside]
    rfl
  · change originalRowCoefficient parameters 0 lower
      ((L : ℂ)⁻¹ • completedDivisionRow (power := 0) (radial := 0) lower positive bounded parameters (by omega) (source 3)) radius mode =
        angularCoefficient ((L : ℂ)⁻¹ • originalDividedCell parameters large (source 3) mode.2 radius
          (positive.le.trans inside.1) inside.2) mode.1
    rw [scalar, angularCoefficient_smul_continuous, fourth _ inside]
    rfl

end Grad.SourceCollarFullSource
