import ACP14GenuineFourierRotation

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1400000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

/-- The RF entering AD10 is the genuine angular derivative of the original
Cartesian frame, on the full closed disk and at every physical length. -/
theorem originalPhysicalFrameMatrix_orbit_hasDerivAt (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : ACore parameters 3) (axialAngle : ℝ)
    (point : ClosedDisk) (angle : ℝ) (row column : Fin 3) :
    HasDerivAt (fun time : ℝ => originalPhysicalFrameMatrix parameters L epsilon field axialAngle
      (rotatedPoint time point) row column)
      ((rotatedPhysicalFrameMatrix parameters 1 1 epsilon field axialAngle (rotatedPoint angle point) *
        Matrix.diagonal ![1, 1, (L : ℂ)⁻¹]) row column) angle := by
  let family := actualFrameFamily parameters 1 1 epsilon field
  let coherent := actualFrameFamily_coherent parameters (unitDiskAdmissible parameters) epsilon field
  let value := physicalColumnScale L (operatorBasis column)
  have derivative := coefficientPhysicalValue_orbit_hasDerivAt parameters family coherent value axialAngle point angle
  rw [coefficientPhysicalValue_rotation_series] at derivative
  let projection : PhysicalValue 3 →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 3 => ℂ) row
  have scalar := (projection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt angle derivative
  have withReference := scalar.const_add (referenceFrame (operatorBasis column) row)
  have equality : (fun time : ℝ => referenceFrame (operatorBasis column) row +
      projection (coefficientPhysicalValue (family 0) axialAngle (rotatedPoint time point) value)) =
      (fun time : ℝ => originalPhysicalFrameMatrix parameters L epsilon field axialAngle
        (rotatedPoint time point) row column) := by
    funext time
    dsimp only [family, value, projection]
    rw [unitFrameFamily_physicalValue]
    change _ = (referenceFrame + originalPhysicalFrameDeviation parameters L epsilon field axialAngle
      (rotatedPoint time point)) (operatorBasis column) row
    rw [← originalPhysicalFrameDeviation_columnScale parameters L epsilon field axialAngle
      (rotatedPoint time point)]
    rfl
  change HasDerivAt (fun time : ℝ => referenceFrame (operatorBasis column) row +
    projection (coefficientPhysicalValue (family 0) axialAngle (rotatedPoint time point) value)) _ angle at withReference
  rw [equality] at withReference
  convert withReference using 1
  let derivativeOperator : OperatorValue 3 3 :=
    (-( (rotatedPoint angle point).val 1 : ℂ)) •
      (∑' cell : ℤ, fourierPhase cell axialAngle •
        coefficientDerivative (family 1) cell firstSpatialIndex (rotatedPoint angle point)) +
    ((rotatedPoint angle point).val 0 : ℂ) •
      (∑' cell : ℤ, fourierPhase cell axialAngle •
        coefficientDerivative (family 1) cell secondSpatialIndex (rotatedPoint angle point))
  change (operatorMatrix derivativeOperator * Matrix.diagonal ![1, 1, (L : ℂ)⁻¹]) row column = _
  have scale : operatorMatrix (physicalColumnScale L) = Matrix.diagonal ![1, 1, (L : ℂ)⁻¹] :=
    operatorMatrix_matrixOperator _
  rw [← scale, ← operatorMatrix_comp]
  change derivativeOperator value row = _
  change (-( (rotatedPoint angle point).val 1 : ℂ)) *
      ((∑' cell : ℤ, fourierPhase cell axialAngle •
        coefficientDerivative (family 1) cell firstSpatialIndex (rotatedPoint angle point)) value row) +
    ((rotatedPoint angle point).val 0 : ℂ) *
      ((∑' cell : ℤ, fourierPhase cell axialAngle •
        coefficientDerivative (family 1) cell secondSpatialIndex (rotatedPoint angle point)) value row) =
    ((rotatedPoint angle point).val 0 : ℂ) *
      ((∑' cell : ℤ, fourierPhase cell axialAngle •
        coefficientDerivative (family 1) cell secondSpatialIndex (rotatedPoint angle point)) value row) -
    ((rotatedPoint angle point).val 1 : ℂ) *
      ((∑' cell : ℤ, fourierPhase cell axialAngle •
        coefficientDerivative (family 1) cell firstSpatialIndex (rotatedPoint angle point)) value row)
  ring

end Grad.ActualCurrentPrimitives
