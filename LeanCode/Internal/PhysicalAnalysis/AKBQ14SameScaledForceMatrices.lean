import AKBQ13SameScaledRotationSeries
import AKBQ11SameScaledCofactorMatrix
import ACP2ForceMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives

variable {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)

 theorem scaledLedgerRotation_native (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix ledger.val.rotatedFrame grade angle point =
      familyMatrix (originalRotatedFamily parameters L epsilon field) grade angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) :=
  (ledger.property.2.2.2.2.2.2.2.1 grade angle point).trans
    (scaledRotatedFrame_original parameters admissible epsilon field grade angle point)

include low

/-- The exact planar force matrix is selected after the complete native RF^T F^-T product. -/
theorem scaledLedgerPlanarForce_native (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix ledger.val.rotatedPlanarProduct grade angle point =
      planarFrameColumns.transpose * familyMatrix (forceMatrixFamily parameters L epsilon field) grade angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) := by
  have formula := ledger.property.2.2.2.2.2.2.2.2.1 grade angle point
  change familyMatrix ledger.val.rotatedPlanarProduct grade angle point =
    (rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point * planarFrameColumns).transpose *
      (familyMatrix ledger.val.frameInverse grade angle point).transpose at formula
  rw [scaledRotatedFrame_original parameters admissible epsilon field grade,
    scaledLedgerInverse_original ledger,Matrix.transpose_mul,Matrix.mul_assoc] at formula
  rw [forceMatrixFamily_matrix parameters L rho epsilon field low]
  exact formula

/-- The exact third force matrix retains the same full native coefficient product and physical length. -/
theorem scaledLedgerThirdForce_native (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix ledger.val.rotatedThirdProduct grade angle point =
      thirdFrameColumn.transpose * familyMatrix (forceMatrixFamily parameters L epsilon field) grade angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) := by
  have formula := ledger.property.2.2.2.2.2.2.2.2.2 grade angle point
  change familyMatrix ledger.val.rotatedThirdProduct grade angle point =
    (rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point * thirdFrameColumn).transpose *
      (familyMatrix ledger.val.frameInverse grade angle point).transpose at formula
  rw [scaledRotatedFrame_original parameters admissible epsilon field grade,
    scaledLedgerInverse_original ledger,Matrix.transpose_mul,Matrix.mul_assoc] at formula
  rw [forceMatrixFamily_matrix parameters L rho epsilon field low]
  exact formula

end Grad.ActualScaledNativeCoefficients
