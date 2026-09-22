import AKBL32SameRoughNativeGaugeConsumer
import SCC7ActualSignedCofactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

/-- The stored normalized frame evaluates the original frame at the same physical point. -/
theorem scaledFrame_original {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) :
    physicalFrameMatrix parameters L ell epsilon field angle point =
      originalPhysicalFrameMatrix parameters L epsilon field angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) := by
  let scaled := physicalScaledPoint ell admissible.2.2.2.1.le
    (admissible.2.2.2.2.trans (min_le_left _ _)) point
  have each (cell : ℤ) : coefficientValue (actualFrameFamily parameters L ell epsilon field 0) cell point =
      frameDeviationCell parameters L epsilon (GradeCore.ofCoreLinear (grade := 4) field) cell scaled :=
    actualFrameDeviationCoefficient_value parameters admissible epsilon
      (GradeCore.ofCoreLinear (grade := 4) field) cell point
  have same : fourierEvaluation (actualFrameFamily parameters L ell epsilon field 0) angle point =
      originalPhysicalFrameDeviation parameters L epsilon field angle scaled := by
    unfold fourierEvaluation
    simp_rw [each]
    exact (originalFrameCells_hasSum parameters L epsilon field angle scaled).tsum_eq
  exact congrArg (fun value => operatorMatrix (referenceFrame + value)) same

/-- Every actual ledger inverse is the original matrix inverse at that same scaled point. -/
theorem scaledLedgerInverse_original {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix ledger.val.frameInverse grade angle point =
      (originalPhysicalFrameMatrix parameters L epsilon field angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point))⁻¹ := by
  have inverse := (ledger.property.2.1 grade angle point).1
  rw [scaledFrame_original parameters admissible epsilon field angle point] at inverse
  exact (Matrix.inv_eq_right_inv inverse).symm

end Grad.ActualScaledNativeCoefficients
