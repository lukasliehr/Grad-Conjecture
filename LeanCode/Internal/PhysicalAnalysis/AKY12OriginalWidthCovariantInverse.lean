import AKY11ActualCellReductionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianUncompressed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualAngularInverse Grad.RawCircularSectors

variable {L sigma gamma ell : ℝ}

/-- One full-cell, original-width smooth Z1, using the accepted actual angular
inverses. The helicity shifts are those of R-J, not R+J. -/
def apCovariantAngularInverse (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (apShiftInverseLinear admissible 2 (-1)).comp (apSmoothValueMap L sigma gamma ell positiveHelicity) +
    (apShiftInverseLinear admissible 2 1).comp (apSmoothValueMap L sigma gamma ell negativeHelicity)

theorem apCovariantAngularInverse_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (cell : ℤ) :
    apSmoothJet admissible 2 cell (apCovariantAngularInverse admissible field) =
      covariantAngularInverse (apSmoothJet admissible 2 cell field) := by
  have positive := (apShiftInverse_jet admissible (-1)
    (apSmoothValueMap L sigma gamma ell positiveHelicity field) cell).trans
      (congrArg (shiftInverseJet (-1)) (apSmoothValueMap_jet admissible positiveHelicity field cell))
  have negative := (apShiftInverse_jet admissible 1
    (apSmoothValueMap L sigma gamma ell negativeHelicity field) cell).trans
      (congrArg (shiftInverseJet 1) (apSmoothValueMap_jet admissible negativeHelicity field cell))
  exact (map_add (apSmoothJet admissible 2 cell) _ _).trans (congrArg₂ Add.add positive negative)

/-- Every original AP grade is bounded at the same analytic width and scale. -/
theorem apCovariantAngularInverse_bound (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apCovariantAngularInverse admissible field)‖ ≤
      (angularInverseConstant grade * (‖positiveHelicity‖ + ‖negativeHelicity‖)) *
        ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  have positive := (apShiftInverse_bound admissible (-1) grade
    (apSmoothValueMap L sigma gamma ell positiveHelicity field)).trans
      (mul_le_mul_of_nonneg_left (apSmoothValueMap_bound positiveHelicity field grade)
        (angularInverseConstant_nonnegative grade))
  have negative := (apShiftInverse_bound admissible 1 grade
    (apSmoothValueMap L sigma gamma ell negativeHelicity field)).trans
      (mul_le_mul_of_nonneg_left (apSmoothValueMap_bound negativeHelicity field grade)
        (angularInverseConstant_nonnegative grade))
  have expanded := (apSmoothGrade L sigma gamma ell 2 grade).map_add
    (apShiftInverse admissible (-1) (apSmoothValueMap L sigma gamma ell positiveHelicity field))
    (apShiftInverse admissible 1 (apSmoothValueMap L sigma gamma ell negativeHelicity field))
  exact (congrArg norm expanded).le.trans ((norm_add_le _ _).trans
    ((add_le_add positive negative).trans_eq (by ring)))

end Grad.CartesianUncompressed
