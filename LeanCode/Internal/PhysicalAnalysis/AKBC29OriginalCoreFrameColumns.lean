import AKBC28SameNegativeForceProduct
import ACP15PhysicalFrameRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FinitePhysicalJetLift Grad.OriginalKernelRetainedDecay
open Grad.SourceCollar Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.GaugeTransfer

def originalFrameColumnCore (parameters : PhaseParameters) (length epsilon : ℝ)
    (base : ACore parameters 3) (column : Fin 3) : ACore parameters 3 :=
  ![partialCore parameters 0 (planarReferenceCore parameters+base),
    partialCore parameters 1 (planarReferenceCore parameters+base),
    (length : ℂ)⁻¹ • affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+base,0)] column

theorem originalFrameColumnCore_value (parameters : PhaseParameters) (length epsilon : ℝ)
    (nonzero : length≠0) (base : ACore parameters 3) (column : Fin 3)
    (point : ClosedDisk) (axial : ℝ) (row : Fin 3) :
    coreValue (originalFrameColumnCore parameters length epsilon base column) point axial row=
      originalPhysicalFrameMatrix parameters length epsilon base axial point row column := by
  fin_cases column
  · exact originalTotalFirstDerivative_frame parameters length epsilon base 0 point axial row
  · exact originalTotalFirstDerivative_frame parameters length epsilon base 1 point axial row
  · change coreValue ((length : ℂ)⁻¹ • affineStateCore parameters length
      ((epsilon : ℂ),planarReferenceCore parameters+base,0)) point axial row=_
    rw [coreValue_smul]
    exact (originalFrame_axialColumn parameters length epsilon nonzero base point axial row).symm

/-- Each R F column is the R derivative of its own original ACore column;
the full RF matrix and the original length normalization are unchanged. -/
theorem originalRotatedFrameColumnCore_value (parameters : PhaseParameters) (length epsilon : ℝ)
    (nonzero : length≠0) (base : ACore parameters 3) (column : Fin 3)
    (point : ClosedDisk) (axial : ℝ) (row : Fin 3) :
    coreValue (rotationCore parameters (originalFrameColumnCore parameters length epsilon base column)) point axial row=
      (rotatedPhysicalFrameMatrix parameters 1 1 epsilon base axial point *
        Matrix.diagonal ![1,1,(length : ℂ)⁻¹]) row column := by
  have derivative := originalCoreOrbit_hasDerivAt parameters
    (originalFrameColumnCore parameters length epsilon base column) point axial 0
  let projection : ComplexEuclidean 3 →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 3 => ℂ) row
  have scalar := (projection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 derivative
  have actual := originalPhysicalFrameMatrix_orbit_hasDerivAt parameters length epsilon base axial point 0 row column
  have same : (fun time => coreValue (originalFrameColumnCore parameters length epsilon base column)
      (rotatedPoint time point) axial row)=
      (fun time => originalPhysicalFrameMatrix parameters length epsilon base axial (rotatedPoint time point) row column) :=
    funext (fun time => originalFrameColumnCore_value parameters length epsilon nonzero base column (rotatedPoint time point) axial row)
  change HasDerivAt (fun time => coreValue (originalFrameColumnCore parameters length epsilon base column)
    (rotatedPoint time point) axial row)
    (coreValue (rotationCore parameters (originalFrameColumnCore parameters length epsilon base column))
      (rotatedPoint 0 point) axial row) 0 at scalar
  rw [same] at scalar
  have equality := scalar.unique actual
  simpa only [rotatedPoint_zero] using equality

end Grad.OriginalKernelCovariantRecovery
