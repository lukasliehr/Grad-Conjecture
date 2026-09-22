import AKDE6LiteralPhysicalOperators
import AKDE4RealNormalizedChart

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open Set
open scoped ContDiff ComplexConjugate

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.OriginalParameterEvaluation Grad.DiskExtension.Operator

variable {dimension : ℕ} {parameters : PhaseParameters}

/-- Reality of the SAME original closed physical field on its actual circle. -/
theorem originalPhysicalClosedJet_real (field : ACore parameters dimension)
    (real : cartesianCoreConjugation parameters field = field) :
    IsRealDiskCellField (originalPhysicalClosedJet parameters field) := by
  intro point coordinate
  rcases point with ⟨disk,circle⟩
  induction circle using QuotientAddGroup.induction_on with
  | H cell =>
    have gradeReal : GradeCoreReality parameters (GradeCore.ofCoreLinear (grade := 0) field) :=
      (gradeCoreConjugation_fixed_iff_reality parameters _).1 (congrArg GradeCore.ofCoreLinear real)
    exact congrArg (fun value : ComplexEuclidean dimension => value coordinate)
      (originalPhysicalEvaluationLift_real parameters (GradeCore.ofCoreLinear (grade := 0) field) gradeReal disk cell)

/-- The actual P09 extension preserves reality everywhere, by its existing
real extension law. The original coefficients and fixed collar are unchanged. -/
theorem originalExtendedField_real (field : ACore parameters dimension)
    (real : cartesianCoreConjugation parameters field = field) (point : SpatialCell) :
    cartesianPhysicalConjugation dimension (originalExtendedField parameters field point) =
      originalExtendedField parameters field point := by
  have actual := ambientExtension_real (originalPhysicalClosedJet parameters field)
    (originalPhysicalClosedJet_real field real) (planarPart point) (point 2 : CellCircle)
  apply PiLp.ext
  exact actual

theorem originalRealExtendedField_complexification (field : ACore parameters dimension)
    (real : cartesianCoreConjugation parameters field = field) (point : SpatialCell) :
    physicalComplexification dimension (originalRealExtendedField parameters field point) =
      originalExtendedField parameters field point :=
  physicalComplexification_realPart dimension _ (originalExtendedField_real field real point)

end Grad.OriginalCellFamily
