import AKBJ5OriginalSourceCartesianCells
import AKBK7OriginalForceAngularContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.Ledger

def thirdRowValue (length : ℝ) (rotation : ComplexEuclidean 3) (axial correction : ComplexEuclidean 1) : ComplexEuclidean 1 :=
  (length : ℂ) • matrixUnit (0 : Fin 1) (2 : Fin 3) rotation - axial + correction

theorem thirdRowValue_component (length : ℝ) (rotation : ComplexEuclidean 3) (axial correction : ComplexEuclidean 1) :
    thirdRowValue length rotation axial correction 0 = (length : ℂ) * rotation 2 - axial 0 + correction 0 := by
  simp [thirdRowValue,matrixUnit_apply,operatorBasis,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]

/-- Axial Fourier extraction acts only after the full third-force output has been formed. -/
theorem thirdRowValue_axialCell (length : ℝ)
    (rotation : ℝ → ComplexEuclidean 3) (axial correction : ℝ → ComplexEuclidean 1)
    (rotationContinuous : Continuous rotation) (axialContinuous : Continuous axial) (correctionContinuous : Continuous correction) (cell : ℤ) :
    angularCoefficient (fun angle => thirdRowValue length (rotation angle) (axial angle) (correction angle)) cell =
      thirdRowValue length (angularCoefficient rotation cell) (angularCoefficient axial cell) (angularCoefficient correction cell) := by
  let mapping : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 1 := (length : ℂ) • matrixUnit (0 : Fin 1) (2 : Fin 3)
  have mappedContinuous := mapping.continuous.comp rotationContinuous
  change angularCoefficient (fun angle => mapping (rotation angle) - axial angle + correction angle) cell =
    mapping (angularCoefficient rotation cell) - angularCoefficient axial cell + angularCoefficient correction cell
  have added := angularCoefficient_add_general (fun angle => mapping (rotation angle) - axial angle) correction
    (mappedContinuous.sub axialContinuous) correctionContinuous cell
  have subtracted := angularCoefficient_sub_general (fun angle => mapping (rotation angle)) axial
    mappedContinuous axialContinuous cell
  have mapped := angularCoefficient_valueMap mapping rotation rotationContinuous cell
  exact added.trans (congrArg (· + angularCoefficient correction cell)
    (subtracted.trans (congrArg (· - angularCoefficient axial cell) mapped)))


end Grad.ActualScalarWeakEquations
