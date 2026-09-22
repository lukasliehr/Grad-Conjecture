import ANV13ReconstructionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse
variable {L sigma gamma ell : ℝ}

def apFullB (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 1 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  LinearMap.id + (4 : ℂ) • (apShiftInverseLinear admissible 1 0).comp (apShiftInverseLinear admissible 1 0)

theorem apFullB_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apFullB admissible field) =
      apSmoothJet admissible 1 cell field + (4 : ℂ) •
        shiftInverseJet 0 (shiftInverseJet 0 (apSmoothJet admissible 1 cell field)) := by
  let project := apSmoothJet admissible 1 cell
  have nested := (apShiftInverse_jet admissible 0 (apShiftInverse admissible 0 field) cell).trans
    (congrArg (shiftInverseJet 0) (apShiftInverse_jet admissible 0 field cell))
  exact (project.map_add field ((4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 field))).trans
    (congrArg (fun value : ClosedJet 1 => project field + value)
      ((project.map_smul (4 : ℂ) _).trans (congrArg (fun value : ClosedJet 1 => (4 : ℂ) • value) nested)))

def fullBConstant (grade : ℕ) : ℝ := 1 + 4 * angularInverseConstant grade ^ 2

theorem fullBConstant_nonnegative (grade : ℕ) : 0 ≤ fullBConstant grade := by
  unfold fullBConstant
  positivity

private theorem original_B_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (field inverse : E) (constant : ℝ) (estimate : ‖inverse‖ ≤ constant ^ 2 * ‖field‖) :
    ‖field + (4 : ℂ) • inverse‖ ≤ (1 + 4 * constant ^ 2) * ‖field‖ := by
  have bound := norm_add_le field ((4 : ℂ) • inverse)
  rw [norm_smul] at bound
  norm_num at bound
  nlinarith

theorem apFullB_bound (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (apFullB admissible field)‖ ≤
      fullBConstant grade * ‖apSmoothGrade L sigma gamma ell 1 grade field‖ := by
  let project := apSmoothGrade L sigma gamma ell 1 grade
  have nested := (apShiftInverse_bound admissible 0 grade (apShiftInverse admissible 0 field)).trans
    (mul_le_mul_of_nonneg_left (apShiftInverse_bound admissible 0 grade field) (angularInverseConstant_nonnegative grade))
  have square : ‖project (apShiftInverse admissible 0 (apShiftInverse admissible 0 field))‖ ≤
      angularInverseConstant grade ^ 2 * ‖project field‖ := nested.trans_eq (by ring)
  have equation := (project.map_add field ((4 : ℂ) • apShiftInverse admissible 0 (apShiftInverse admissible 0 field))).trans
    (congrArg (fun value => project field + value) (project.map_smul (4 : ℂ) _))
  exact (congrArg norm equation).le.trans (original_B_bound _ _ _ square)

end Grad.ActualScalarForcing
