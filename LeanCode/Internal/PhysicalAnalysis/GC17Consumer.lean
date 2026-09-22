import GC17Proof

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Ledger.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

theorem actualCoefficientLedger_ready : ActualLedgerGoal := actualLedger

/-- Immediate AO28 consumer: the cofactor coefficient comes from the constructed
original-state ledger, and reconstructs the literal det(F) F^-1 F^-T + I. -/
theorem actualCofactorValue {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (frameBase : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (seedBase : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let ledger := physicalLedger parameters admissible rho alpha delta parameter epsilon field frameBase seedBase
    let inverse := operatorMatrix (coefficientPhysicalValue (ledger.val.frameInverse grade) angle point)
    operatorMatrix (coefficientPhysicalValue (ledger.val.fluxDeviation grade) angle point) =
      (physicalFrameMatrix parameters L ell epsilon field angle point).det • (inverse * inverse.transpose) + 1 := by
  exact (physicalLedger parameters admissible rho alpha delta parameter epsilon field frameBase seedBase).property.2.2.2.2.2.1
    grade angle point

/-- Immediate AQ15 consumer, with the actual Cartesian rotation of the frame. -/
theorem actualPlanarRotationValue {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (frameBase : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (seedBase : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let ledger := physicalLedger parameters admissible rho alpha delta parameter epsilon field frameBase seedBase
    operatorMatrix (coefficientPhysicalValue (ledger.val.rotatedPlanarProduct grade) angle point) =
      (rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point * planarFrameColumns).transpose *
        (operatorMatrix (coefficientPhysicalValue (ledger.val.frameInverse grade) angle point)).transpose := by
  exact (physicalLedger parameters admissible rho alpha delta parameter epsilon field frameBase seedBase).property.2.2.2.2.2.2.2.2.1
    grade angle point

end Grad.GaugeCoefficients.Physical.Ledger.Consumer
