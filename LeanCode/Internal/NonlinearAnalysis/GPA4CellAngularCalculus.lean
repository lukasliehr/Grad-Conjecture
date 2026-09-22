import GPA3CharacterAngularBounds

noncomputable section
open scoped BigOperators ContDiff
namespace Grad.ActualPhysicalAngular
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem angularCharacterField_periodic {dimension : ℕ} (shift : ℤ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (periodic : Function.Periodic field (0, 2 * Real.pi)) :
    Function.Periodic (angularCharacterField shift field) (0, 2 * Real.pi) := by
  intro point
  simp only [angularCharacterField, Prod.snd_add, ← cellCharacter_coe, AddCircle.coe_add_period]
  rw [periodic point]

theorem angularJet_one_finsetSum {Index : Type*} {dimension : ℕ} (indices : Finset Index)
    (fields : Index → ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ∀ index ∈ indices, ContDiff ℝ ∞ (fields index)) (radius angle : ℝ) :
    angularJet 1 (∑ index ∈ indices, fields index) (radius, angle) =
      ∑ index ∈ indices, angularJet 1 (fields index) (radius, angle) := by
  have totalSmooth : ContDiff ℝ ∞ (∑ index ∈ indices, fields index) := by
    simpa only [← Finset.sum_apply] using ContDiff.sum smooth
  have first := angularJet_hasDerivAt 0 _ totalSmooth radius angle
  have second := HasDerivAt.sum (u := indices) (fun index member =>
    angularJet_hasDerivAt 0 (fields index) (smooth index member) radius angle)
  simp only [angularJet_zero] at first second
  have equality : (∑ index ∈ indices, fun angular => fields index (radius, angular)) =
      (fun angular => (∑ index ∈ indices, fields index) (radius, angular)) := by
    funext angular
    simp only [Finset.sum_apply]
  rw [equality] at second
  exact first.unique second

def scalarCellValue (field : ℝ × ℝ → ComplexEuclidean 1) (radius : ℝ) (angle : ℝ) : ℂ :=
  field (radius, angle) 0

def scalarCellAngular (field : ℝ × ℝ → ComplexEuclidean 1) (radius : ℝ) (angle : ℝ) : ℂ :=
  angularJet 1 field (radius, angle) 0

theorem scalarCellAngular_hasDerivAt (field : ℝ × ℝ → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    HasDerivAt (scalarCellValue field radius) (scalarCellAngular field radius angle) angle := by
  have derivative := angularJet_hasDerivAt 0 field smooth radius angle
  rw [angularJet_zero] at derivative
  exact ((PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : ComplexEuclidean 1 →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt angle derivative

theorem scalarCellAngular_fourier (field : ℝ × ℝ → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ field) (periodic : Function.Periodic field (0, 2 * Real.pi))
    (radius : ℝ) (mode : ℤ) :
    angularCoefficient (scalarCellAngular field radius) mode =
      (Complex.I * (mode : ℂ)) * angularCoefficient (scalarCellValue field radius) mode := by
  let projection : ComplexEuclidean 1 →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0
  apply angularCoefficient_scalar_derivative
  · exact projection.continuous.comp (smooth.continuous.comp (continuous_const.prodMk continuous_id))
  · exact projection.continuous.comp ((angularJet_smooth 1 field smooth).continuous.comp (continuous_const.prodMk continuous_id))
  · exact scalarCellAngular_hasDerivAt field smooth radius
  · have endpoint := angularJet_endpoint 0 field periodic radius
    rw [angularJet_zero] at endpoint
    exact congrArg (fun value : ComplexEuclidean 1 => value 0) endpoint

end Grad.ActualPhysicalAngular
