import AKDE9OriginalScalarOperators
import AKU55LiteralDeterminantFourierValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
open Set MeasureTheory
open scoped ContDiff Interval

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient Grad.RawForward
open Grad.Constraints Grad.QuotientProjection Grad.FinitePhysicalJetLift Grad.AxisSplit

variable {parameters : PhaseParameters}

theorem originalScalarCell_sub (first second : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    originalScalarCell (first-second) point.val cell =
      originalScalarCell first point.val cell - originalScalarCell second point.val cell := by
  unfold originalScalarCell
  rw [originalCellField_coreValue,originalCellField_coreValue,originalCellField_coreValue,
    Grad.GaugeCoefficients.Physical.RadialLedger.coreValue_subtract]
  rfl

theorem originalScalarCell_add (first second : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    originalScalarCell (first+second) point.val cell =
      originalScalarCell first point.val cell + originalScalarCell second point.val cell := by
  unfold originalScalarCell
  rw [originalCellField_coreValue,originalCellField_coreValue,originalCellField_coreValue,coreValue_add]
  rfl

theorem originalScalarCell_dot (first second : ACore parameters 3) (point : ClosedDisk) (cell : ℝ) :
    originalScalarCell (dotOperation parameters first second) point.val cell =
      complexDot (originalCellField first point.val cell) (originalCellField second point.val cell) := by
  unfold originalScalarCell
  rw [originalCellField_coreValue,originalCellField_coreValue,originalCellField_coreValue,coreValue_dotOperation]

theorem originalScalarCell_determinant (first second third : ACore parameters 3) (point : ClosedDisk) (cell : ℝ) :
    originalScalarCell (determinantOperation parameters first second third) point.val cell =
      complexDeterminant (originalCellField first point.val cell) (originalCellField second point.val cell)
        (originalCellField third point.val cell) := by
  unfold originalScalarCell
  rw [originalCellField_coreValue,originalCellField_coreValue,originalCellField_coreValue,originalCellField_coreValue,
    coreValue_determinantOperation]

theorem complexRemoveAngularAverage_closed_congr (first second : SpatialPlane → ℝ → ℂ)
    (same : ∀ point : ClosedDisk, ∀ cell, first point.val cell = second point.val cell)
    (point : ClosedDisk) (cell : ℝ) :
    complexRemoveAngularAverage first point.val cell = complexRemoveAngularAverage second point.val cell := by
  unfold complexRemoveAngularAverage complexAngularAverage
  rw [same point cell]
  congr 2
  apply intervalIntegral.integral_congr
  intro angle _
  exact same ⟨planeRotationAction angle point.val,by
    change ‖planeRotationAction angle point.val‖ ≤ 1
    rw [physicalRotation_norm]
    exact point.property⟩ cell

theorem originalScalarCell_radius (point : ClosedDisk) (cell : ℝ) :
    originalScalarCell (radiusSquaredCore parameters (scalarConstantCore parameters 1)) point.val cell =
      (‖point.val‖ ^ 2 : ℝ) := by
  unfold originalScalarCell
  rw [originalCellField_coreValue]
  have radiusValue : coreValue (radiusSquaredCore parameters (scalarConstantCore parameters 1)) point cell =
      ‖point.val‖ ^ 2 • coreValue (scalarConstantCore parameters 1) point cell := by
    unfold coreValue
    simp_rw [radiusSquaredCore_value,smul_comm (axialPhase _ cell) (‖point.val‖^2)]
    exact tsum_const_smul'' (‖point.val‖^2)
  rw [radiusValue]
  change (‖point.val‖^2 • coreValue (constantCore parameters (EuclideanSpace.single 0 1)) point cell) 0 = _
  rw [coreValue_constant]
  simp

/-- The four original core equations evaluate to the literal real-geometry
complex raw rows, on the full closed disk. No angular-mean premise is added. -/
theorem originalRawRowsCore_physical (length epsilon : ℝ) (vector : ACore parameters 3)
    (potential : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    (fun row => originalScalarCell (originalRawRowsCore parameters length ((epsilon:ℂ),vector,potential) row) point.val cell) =
      complexRawRows length epsilon (originalCellField vector) (originalScalarCell potential) point.val cell := by
  funext row
  fin_cases row
  · change originalScalarCell (rotationCore parameters potential -
        dotOperation parameters (rotationCore parameters vector) (rotationCore parameters vector) +
        radiusSquaredCore parameters (scalarConstantCore parameters 1)) point.val cell = _
    rw [originalScalarCell_add,originalScalarCell_sub,originalScalarCell_dot,originalScalarCell_radius]
    exact congrArg₂ (fun first second : ℂ => first-second+(‖point.val‖^2:ℝ))
      (originalScalarCell_rotation potential point cell).symm
      (congrArg (fun value => complexDot value value) (originalCellField_rotation vector point cell).symm)
  · change originalScalarCell (removeAngularCore parameters (eulerCore parameters potential -
        dotOperation parameters (eulerCore parameters vector) (rotationCore parameters vector))) point.val cell = _
    rw [← originalScalarCell_removeMean]
    change complexRemoveAngularAverage _ point.val cell = complexRemoveAngularAverage
      (fun argument axial => diskEuler (originalScalarCell potential) argument axial -
        complexDot (diskEuler (originalCellField vector) argument axial) (diskAngular (originalCellField vector) argument axial)) point.val cell
    apply complexRemoveAngularAverage_closed_congr
    intro disk axial
    rw [originalScalarCell_sub,originalScalarCell_dot,← originalScalarCell_euler,
      ← originalCellField_euler,← originalCellField_rotation]
  · change originalScalarCell (removeAngularCore parameters (dotOperation parameters (rotationCore parameters vector)
        (affineStateCore parameters length ((epsilon:ℂ),vector,potential)) - timeDerivativeCore parameters potential)) point.val cell = _
    rw [← originalScalarCell_removeMean]
    change complexRemoveAngularAverage _ point.val cell = complexRemoveAngularAverage
      (fun argument axial => complexDot (diskAngular (originalCellField vector) argument axial)
        (complexAffineStateDerivative length epsilon (originalCellField vector) argument axial) -
        cellDerivative (originalScalarCell potential) argument axial) point.val cell
    apply complexRemoveAngularAverage_closed_congr
    intro disk axial
    rw [originalScalarCell_sub,originalScalarCell_dot,← originalCellField_rotation,
      ← originalCellField_affine,← originalScalarCell_cellDerivative]
  · change originalScalarCell (removeAngularCore parameters (determinantOperation parameters (eulerCore parameters vector)
        (rotationCore parameters vector) (affineStateCore parameters length ((epsilon:ℂ),vector,potential)))) point.val cell = _
    rw [← originalScalarCell_removeMean]
    change complexRemoveAngularAverage _ point.val cell = complexRemoveAngularAverage
      (fun argument axial => complexDeterminant (diskEuler (originalCellField vector) argument axial)
        (diskAngular (originalCellField vector) argument axial)
        (complexAffineStateDerivative length epsilon (originalCellField vector) argument axial)) point.val cell
    apply complexRemoveAngularAverage_closed_congr
    intro disk axial
    rw [originalScalarCell_determinant,← originalCellField_euler,← originalCellField_rotation,← originalCellField_affine]

end Grad.OriginalCellFamily
