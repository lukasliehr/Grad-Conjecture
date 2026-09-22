import SBT5OriginalSource
import GQ3RotationCore

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace
open Grad.NonlinearQuotientBounds Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem boundaryDiskPoint_rotation_zero (angle : ℝ) :
    Grad.GaugeCoefficients.Radial.rotatedPoint angle (boundaryDiskPoint (0 : CellCircle)) =
      boundaryDiskPoint (angle : CellCircle) := by
  apply Subtype.ext
  change Grad.GaugeCoefficients.Radial.planeRotation angle (boundaryCirclePoint (0 : CellCircle)) =
    boundaryCirclePoint (angle : CellCircle)
  rw [show (0 : CellCircle) = ((0 : ℝ) : CellCircle) from rfl, boundaryCirclePoint_coe, boundaryCirclePoint_coe]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [Grad.GaugeCoefficients.Radial.planeRotation, collarPlane]

theorem boundaryDiskPoint_pi : boundaryDiskPoint (Real.pi : CellCircle) =
    boundaryDiskPoint ((-Real.pi : ℝ) : CellCircle) := by
  apply Subtype.ext
  change boundaryCirclePoint (Real.pi : CellCircle) = boundaryCirclePoint ((-Real.pi : ℝ) : CellCircle)
  rw [boundaryCirclePoint_coe, boundaryCirclePoint_coe]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [collarPlane]

theorem closedBoundary_hasDerivAt {dimension : ℕ} (field : ClosedJet dimension) (angle : ℝ) :
    HasDerivAt (fun time : ℝ => field.value (boundaryDiskPoint (time : CellCircle)))
      ((rotationJet field).value (boundaryDiskPoint (angle : CellCircle))) angle := by
  have derivative := closedOrbit_hasDerivAt field (boundaryDiskPoint (0 : CellCircle)) angle
  simpa only [boundaryDiskPoint_rotation_zero] using derivative

theorem originalBoundaryCoefficient_rotation {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    originalBoundaryCoefficient parameters (rotationCore parameters field) mode =
      (Complex.I * (mode.1 : ℂ)) • originalBoundaryCoefficient parameters field mode := by
  change fourierCoeff (fun angle : CellCircle => (rotationJet (field.val mode.2)).value (boundaryDiskPoint angle)) mode.1 =
    (Complex.I * (mode.1 : ℂ)) • fourierCoeff (fun angle : CellCircle => (field.val mode.2).value (boundaryDiskPoint angle)) mode.1
  rw [← angularCoefficient_circle, ← angularCoefficient_circle]
  apply angularCoefficient_derivative
  · exact (field.val mode.2).value.continuous.comp
      (boundaryDiskPoint_continuous.comp (AddCircle.continuous_mk' _))
  · exact (rotationJet (field.val mode.2)).value.continuous.comp
      (boundaryDiskPoint_continuous.comp (AddCircle.continuous_mk' _))
  · exact closedBoundary_hasDerivAt (field.val mode.2)
  · rw [boundaryDiskPoint_pi]

end Grad.SourceBoundaryTrace
