import SCS30PhysicalPolarProjection

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.SourceCollarBulk Grad.FlatSourceProjection Grad.QuotientProjection Grad.AxisCore

def physicalDividedSources (parameters : PhaseParameters) (L : ℝ) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) : Fin 3 → ℝ × ℝ → ComplexEuclidean 1 :=
  ![fun angles => radialProjection angles.1 (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded angles),
    fun angles => tangentialProjection angles.1 (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded angles),
    fun angles => (L : ℂ)⁻¹ • (radius⁻¹ • corePolarValue parameters (source 3) radius nonnegative bounded angles)]

def coreDividedSourceCells (parameters : PhaseParameters) (L : ℝ) (source : SmoothQuotient parameters)
    (cell : ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) : Fin 3 → ℝ → ComplexEuclidean 1 :=
  ![fun angle => radialProjection angle (radius⁻¹ • ((cartesianSourceVector source).val cell).value (polarClosedPoint radius angle nonnegative bounded)),
    fun angle => tangentialProjection angle (radius⁻¹ • ((cartesianSourceVector source).val cell).value (polarClosedPoint radius angle nonnegative bounded)),
    fun angle => (L : ℂ)⁻¹ • (radius⁻¹ • ((source 3).val cell).value (polarClosedPoint radius angle nonnegative bounded))]

theorem physicalDividedSources_continuous (parameters : PhaseParameters) (L : ℝ) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3) :
    Continuous (physicalDividedSources parameters L source radius nonnegative bounded component) := by
  have planar : Continuous (fun angles => radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded angles) :=
    (continuous_const : Continuous (fun _ : ℝ × ℝ => radius⁻¹)).smul
      (corePolarValue_continuous parameters (cartesianSourceVector source) radius nonnegative bounded)
  have fourth : Continuous (fun angles => radius⁻¹ • corePolarValue parameters (source 3) radius nonnegative bounded angles) :=
    (continuous_const : Continuous (fun _ : ℝ × ℝ => radius⁻¹)).smul
      (corePolarValue_continuous parameters (source 3) radius nonnegative bounded)
  fin_cases component
  · exact (radialProjection_continuous.comp continuous_fst).clm_apply planar
  · exact (tangentialProjection_continuous.comp continuous_fst).clm_apply planar
  · exact (continuous_const : Continuous (fun _ : ℝ × ℝ => (L : ℂ)⁻¹)).smul fourth

theorem originalDividedSourceCells_core {grade : ℕ} (parameters : PhaseParameters) (L : ℝ)
    (large : 3 ≤ grade) (source : SmoothQuotient parameters) (cell : ℤ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    originalDividedSourceCells parameters L large (quotientEta parameters grade source) cell radius nonnegative bounded =
      coreDividedSourceCells parameters L source cell radius nonnegative bounded := by
  have planar : originalDividedCell parameters large
      (originalSourcePlanar parameters grade (quotientEta parameters grade source)) cell radius nonnegative bounded =
      (fun angle => radius⁻¹ • ((cartesianSourceVector source).val cell).value (polarClosedPoint radius angle nonnegative bounded)) := by
    funext angle
    unfold originalDividedCell
    rw [originalSourcePlanar_core, completedOriginalCell_core]
    rfl
  have fourth : originalDividedCell parameters large (quotientEta parameters grade source 3) cell radius nonnegative bounded =
      (fun angle => radius⁻¹ • ((source 3).val cell).value (polarClosedPoint radius angle nonnegative bounded)) := by
    funext angle
    unfold originalDividedCell
    rw [show quotientEta parameters grade source 3 = aGradeEta parameters (GradeCore.ofCoreLinear (source 3)) from rfl,
      completedOriginalCell_core]
    rfl
  unfold originalDividedSourceCells
  rw [planar, fourth]
  funext component angle
  fin_cases component
  · exact (radialProjection_apply angle (fun theta => radius⁻¹ •
      ((cartesianSourceVector source).val cell).value (polarClosedPoint radius theta nonnegative bounded))).symm
  · exact (tangentialProjection_apply angle (fun theta => radius⁻¹ •
      ((cartesianSourceVector source).val cell).value (polarClosedPoint radius theta nonnegative bounded))).symm
  · rfl

end Grad.SourceCollarFullSource
