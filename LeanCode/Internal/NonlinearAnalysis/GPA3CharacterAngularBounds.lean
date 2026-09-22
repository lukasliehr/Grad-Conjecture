import GPA2ClosedPolarAngular

noncomputable section
open scoped BigOperators
namespace Grad.ActualPhysicalAngular
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace Grad.SourceCollarCoefficients
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.NonlinearRange

def characterColumnAngularValue {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (column : PhysicalValue input) (shift : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) : PhysicalValue output :=
  ((Complex.I * (shift : ℂ)) * cellExponential shift angle) •
    (coefficientColumnJet parameters family coherent cell column).value (polarClosedPoint radius angle nonnegative bounded) +
  cellExponential shift angle •
    (rotationJet (coefficientColumnJet parameters family coherent cell column)).value (polarClosedPoint radius angle nonnegative bounded)

def characterColumnAngularBudget {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (column : PhysicalValue input) (shift : ℤ) (cell : ℤ) : ℝ :=
  (|(shift : ℝ)| * coefficientCellBudget (family 0) cell + 2 * coefficientCellBudget (family 1) cell) * ‖column‖

theorem characterColumn_hasDerivAt {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (column : PhysicalValue input) (shift : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasDerivAt (fun time => angularCharacterField shift
      (originalPolarValue (coefficientColumnJet parameters family coherent cell column)) (radius, time))
      (characterColumnAngularValue parameters family coherent cell column shift radius angle nonnegative bounded) angle := by
  have derivative := (seedCharacter_hasDerivAt shift angle).smul
    (originalPolar_hasDerivAt (coefficientColumnJet parameters family coherent cell column) radius angle nonnegative bounded)
  convert derivative using 1 <;> first
    | rfl
    | simp only [characterColumnAngularValue,
        originalPolarValue_closed _ radius angle nonnegative bounded, add_comm]

theorem characterColumn_angularJet {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (column : PhysicalValue input) (shift : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    angularJet 1 (angularCharacterField shift (originalPolarValue
      (coefficientColumnJet parameters family coherent cell column))) (radius, angle) =
      characterColumnAngularValue parameters family coherent cell column shift radius angle nonnegative bounded := by
  have derivative := angularJet_hasDerivAt 0 _ (angularCharacterField_smooth shift _
    (originalPolarValue_smooth (coefficientColumnJet parameters family coherent cell column))) radius angle
  rw [angularJet_zero] at derivative
  exact derivative.unique (characterColumn_hasDerivAt parameters family coherent cell column shift radius angle nonnegative bounded)

theorem characterColumnAngularBudget_summable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (column : PhysicalValue input) (shift : ℤ) :
    Summable (characterColumnAngularBudget parameters family column shift) :=
  (((coefficientCellBudget_summable (family 0)).mul_left |(shift : ℝ)|).add
    ((coefficientCellBudget_summable (family 1)).mul_left 2)).mul_right ‖column‖

theorem characterColumnAngularValue_bound {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (cell : ℤ) (column : PhysicalValue input) (shift : ℤ)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ‖characterColumnAngularValue parameters family coherent cell column shift radius angle nonnegative bounded‖ ≤
      characterColumnAngularBudget parameters family column shift cell := by
  have cast : ‖(shift : ℂ)‖ = |(shift : ℝ)| := by norm_cast
  unfold characterColumnAngularValue
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, norm_mul, norm_mul, Complex.norm_I, cellExponential_norm, one_mul, mul_one, one_mul, cast]
  have first := mul_le_mul_of_nonneg_left
    (coefficientColumn_value_bound parameters family coherent cell column (polarClosedPoint radius angle nonnegative bounded))
    (abs_nonneg (shift : ℝ))
  have second := coefficientColumn_rotation_bound parameters family coherent cell column (polarClosedPoint radius angle nonnegative bounded)
  exact (add_le_add first second).trans_eq (by unfold characterColumnAngularBudget; ring)

end Grad.ActualPhysicalAngular
