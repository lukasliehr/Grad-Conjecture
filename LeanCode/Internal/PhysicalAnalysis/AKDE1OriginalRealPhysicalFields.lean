import AKDC6ConstructedOriginalSmoothBranch
import OriginalEvaluationReality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set
open scoped ContDiff ComplexConjugate

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.OriginalParameterEvaluation
open Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization Grad.PhysicalCoordinates

/-- Coordinatewise real part in the literal physical coordinate order. -/
def physicalRealPart (dimension : ℕ) : ComplexEuclidean dimension →L[ℝ] EuclideanSpace ℝ (Fin dimension) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 (fun coordinate => (value coordinate).re)
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        exact Complex.add_re _ _
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        simp }

/-- Real physical vectors are embedded into the same complex coordinates. -/
def physicalComplexification (dimension : ℕ) : EuclideanSpace ℝ (Fin dimension) →L[ℝ] ComplexEuclidean dimension :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 (fun coordinate => ((value coordinate : ℝ) : ℂ))
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        exact Complex.ofReal_add _ _
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        exact Complex.ofReal_mul _ _ }

theorem physicalComplexification_realPart (dimension : ℕ) (value : ComplexEuclidean dimension)
    (real : cartesianPhysicalConjugation dimension value = value) :
    physicalComplexification dimension (physicalRealPart dimension value) = value := by
  apply PiLp.ext
  intro coordinate
  have fixed := congrArg (fun vector : ComplexEuclidean dimension => (vector coordinate).im) real
  change ((value coordinate).re : ℂ) = value coordinate
  apply Complex.ext
  · rfl
  · change (0:ℝ) = (value coordinate).im
    change -(value coordinate).im = (value coordinate).im at fixed
    linarith

/-- The actual real field on the fixed P09 collar. On the original disk,
reality identifies this with the unchanged original Fourier evaluation. -/
def originalRealExtendedField {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) : SpatialCell → EuclideanSpace ℝ (Fin dimension) :=
  fun point => physicalRealPart dimension (originalExtendedField parameters field point)

theorem originalRealExtendedField_smooth {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) : ContDiff ℝ ∞ (originalRealExtendedField parameters field) :=
  (physicalRealPart dimension).contDiff.comp (originalExtendedField_smooth parameters field)

theorem originalRealExtendedField_original {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (real : cartesianCoreConjugation parameters field = field)
    (point : ClosedDisk) (cell : ℝ) :
    physicalComplexification dimension (originalRealExtendedField parameters field (assembleSpatialCell point.val cell)) =
      (originalPhysicalClosedJet parameters field).value (point,(cell : CellCircle)) := by
  unfold originalRealExtendedField
  rw [originalExtendedField_onDisk]
  apply physicalComplexification_realPart
  have gradeReal : GradeCoreReality parameters (GradeCore.ofCoreLinear (grade := 0) field) :=
    (gradeCoreConjugation_fixed_iff_reality parameters _).1 (congrArg GradeCore.ofCoreLinear real)
  exact originalPhysicalEvaluationLift_real parameters (GradeCore.ofCoreLinear (grade := 0) field) gradeReal point cell

theorem originalRealExtendedField_periodic {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (point : EuclideanSpace ℝ (Fin 2)) (cell : ℝ) :
    originalRealExtendedField parameters field (assembleSpatialCell point (cell+2*Real.pi)) =
      originalRealExtendedField parameters field (assembleSpatialCell point cell) := by
  unfold originalRealExtendedField originalExtendedField Grad.DiskExtension.Operator.ambientExtensionCellLift
  simp only [planarPart_assembleSpatialCell]
  have same : (((cell+2*Real.pi:ℝ) : CellCircle)) = ((cell:ℝ) : CellCircle) :=
    AddCircle.coe_add_period (2*Real.pi) cell
  exact congrArg (fun coordinate => physicalRealPart dimension
    (Grad.DiskExtension.Operator.ambientExtensionFromValue (originalPhysicalClosedJet parameters field).value point coordinate)) same

end Grad.OriginalCellFamily
