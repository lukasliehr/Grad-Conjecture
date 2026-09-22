import BCT3BoundaryPolarFamily

noncomputable section

set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- The scalar physical row in covariant polar coordinates. -/
def originalBoundaryRow (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (axialAngle polarAngle : ℝ) (point : ClosedDisk) (component : Fin 3) : ℂ :=
  ((originalPhysicalBoundaryMatrix parameters L rho alpha delta parameter epsilon field
    axialAngle point).mulVec (polarVector component polarAngle)) 0

theorem paddedRow_polarEntry (row : Matrix (Fin 1) (Fin 3) ℂ)
    (angle : ℝ) (component : Fin 3) :
    polarMatrixEntry 2 component angle (thirdFrameColumn * row) =
      (row.mulVec (polarVector component angle)) 0 := by
  simp [polarMatrixEntry, matrixPairing, polarVector, physicalToroidalVector,
    thirdFrameColumn, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Fin.sum_univ_three]

theorem paddedBoundaryFamily_polarEntry (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (grade : ℕ) (axialAngle polarAngle : ℝ) (point : ClosedDisk) (component : Fin 3) :
    polarMatrixEntry 2 component polarAngle
      (familyMatrix (paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field)
        grade axialAngle point) =
      originalBoundaryRow parameters L rho alpha delta parameter epsilon field axialAngle polarAngle point component := by
  have coherent := (originalBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low).actualCoherent
  rw [paddedBoundaryFamily, familyMatrix_comp (unitDiskAdmissible parameters) _ _
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 _) coherent,
    familyMatrix_constant (unitDiskAdmissible parameters),
    originalBoundaryFamily_matrix parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low, paddedRow_polarEntry]
  rfl

theorem paddedBoundaryReference_polarEntry (parameters : PhaseParameters)
    (grade : ℕ) (axialAngle angle : ℝ) (component : Fin 3) :
    polarMatrixEntry 2 component angle
      (familyMatrix (paddedBoundaryReference parameters) grade axialAngle
        (polarClosedPoint 1 angle zero_le_one le_rfl)) =
      if (0 : Fin 3) = component then 1 else 0 := by
  have coherent : FamilyCoherent (referenceBoundaryFamily parameters) :=
    traceFamily_coherent (unitDiskAdmissible parameters) _ _
      (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 2)
      (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 _)
  rw [paddedBoundaryReference, familyMatrix_comp (unitDiskAdmissible parameters) _ _
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 _) coherent,
    familyMatrix_constant (unitDiskAdmissible parameters), referenceBoundaryFamily_matrix,
    paddedRow_polarEntry]
  have trig : (Real.cos angle : ℂ) ^ 2 + (Real.sin angle : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq angle
  fin_cases component <;>
    simp [circleTraceCovector, polarVector, physicalRadialVector,
      physicalTangentialVector, physicalToroidalVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, polarClosedPoint, polarPlane, collarPlane]
  · simpa [pow_two] using trig
  · ring

theorem boundaryPolarDeviation_outer (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (grade : ℕ) (axialAngle angle : ℝ) (component : Fin 3) :
    polarMatrixEntry 2 component angle
      (familyMatrix (boundaryPolarDeviation parameters L rho alpha delta parameter epsilon field)
        grade axialAngle (polarClosedPoint 1 angle zero_le_one le_rfl)) =
      originalBoundaryRow parameters L rho alpha delta parameter epsilon field axialAngle angle
        (polarClosedPoint 1 angle zero_le_one le_rfl) component -
        (if (0 : Fin 3) = component then 1 else 0) := by
  have estimate := paddedBoundaryFamily_estimate parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low
  change polarMatrixEntry 2 component angle
    (familyMatrix (fun q => paddedBoundaryFamily parameters L rho alpha delta parameter epsilon field q -
      paddedBoundaryReference parameters q) grade axialAngle
      (polarClosedPoint 1 angle zero_le_one le_rfl)) = _
  rw [familyMatrix_sub (unitDiskAdmissible parameters) _ _
    estimate.actualCoherent estimate.referenceCoherent, polarMatrixEntry_sub,
    paddedBoundaryFamily_polarEntry parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low, paddedBoundaryReference_polarEntry]

end Grad.ActualBoundaryPrimitives
