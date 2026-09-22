import AKBQ2SameScaledGaugeMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger

/-- The signed B+I flux ledger is the actual original cofactor at y=ell Y; the circular sign is retained. -/
theorem scaledLedgerFlux_original {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix ledger.val.fluxDeviation grade angle point =
      originalPhysicalSignedCofactor parameters L epsilon field angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) + 1 := by
  have formula := ledger.property.2.2.2.2.2.1 grade angle point
  change familyMatrix ledger.val.fluxDeviation grade angle point =
    (physicalFrameMatrix parameters L ell epsilon field angle point).det •
      (familyMatrix ledger.val.frameInverse grade angle point *
        (familyMatrix ledger.val.frameInverse grade angle point).transpose) + 1 at formula
  rw [scaledFrame_original parameters admissible epsilon field,scaledLedgerInverse_original ledger] at formula
  exact formula

/-- The same identity against the existing full native convolution family. -/
theorem scaledLedgerFlux_native {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix ledger.val.fluxDeviation grade angle point =
      familyMatrix (originalCofactorFamily parameters L epsilon field) grade angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) + 1 := by
  rw [scaledLedgerFlux_original ledger,originalCofactorFamily_eq_signedCofactor parameters L rho epsilon field low]

end Grad.ActualScaledNativeCoefficients
