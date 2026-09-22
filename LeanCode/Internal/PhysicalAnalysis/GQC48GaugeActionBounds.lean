import GQC46RemovedGraph

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Frame

theorem apMultiplier_identity_high {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell dimension grade) :
    apMultiplier admissible (identityFamily L sigma gamma ell dimension grade) field = field := by
  apply apPhysicalValue_ext admissible large
  intro angle
  rw [apMultiplier_physical]
  apply ContinuousMap.ext
  intro point
  change coefficientPhysicalValue (identityFamily L sigma gamma ell dimension grade) angle point
    (apPhysicalValue admissible large angle field point) = _
  rw [identityFamily, identityFamily_physicalValue]
  rfl

def gaugeActionConstant {L sigma gamma ell : ℝ} (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : ℝ :=
  apComplementConstant grade * (apMultiplierConstant L sigma gamma grade * ‖fullGaugeFamily gauge grade‖)

def extensionActionConstant {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : ℝ :=
  apMultiplierConstant L sigma gamma grade * ‖complementExtensionFamily admissible gauge grade‖

theorem gaugeActionConstant_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : 0 ≤ gaugeActionConstant gauge grade :=
  mul_nonneg (apComplementConstant_nonnegative grade)
    (mul_nonneg (apMultiplierConstant_nonnegative admissible grade) (norm_nonneg _))

theorem extensionActionConstant_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) : 0 ≤ extensionActionConstant admissible gauge grade :=
  mul_nonneg (apMultiplierConstant_nonnegative admissible grade) (norm_nonneg _)

theorem apGaugeMap_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    ‖apGaugeMap admissible gauge grade field‖ ≤ gaugeActionConstant gauge grade * ‖field‖ := by
  exact (apComplement_bound L sigma gamma ell grade _).trans
    ((mul_le_mul_of_nonneg_left (apMultiplier_bound admissible (fullGaugeFamily gauge grade) field)
      (apComplementConstant_nonnegative grade)).trans_eq (mul_assoc _ _ _).symm)

theorem apExtensionMap_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    ‖apExtensionMap admissible gauge grade field‖ ≤ extensionActionConstant admissible gauge grade * ‖field‖ :=
  apMultiplier_bound admissible (complementExtensionFamily admissible gauge grade) field

theorem apGaugeMap_circle_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) {grade : ℕ} (large : 2 ≤ grade)
    (field : apGrade L sigma gamma ell 3 grade) (circular : apComplement L sigma gamma ell grade field = 0) :
    ‖apGaugeMap admissible gauge grade field‖ ≤
      apComplementConstant grade * (apMultiplierConstant L sigma gamma grade * ‖gauge grade‖) * ‖field‖ := by
  have identity : apGaugeMap admissible gauge grade field =
      apComplement L sigma gamma ell grade (apMultiplier admissible (gauge grade) field) := by
    change apComplement L sigma gamma ell grade
      (apMultiplier admissible (identityFamily L sigma gamma ell 3 grade + gauge grade) field) = _
    have multiplied := (congrArg (fun mapping : apGrade L sigma gamma ell 3 grade →L[ℂ]
      apGrade L sigma gamma ell 3 grade => mapping field)
        (apMultiplier_add admissible (identityFamily L sigma gamma ell 3 grade) (gauge grade))).trans
      (congrArg (fun value : apGrade L sigma gamma ell 3 grade => value + apMultiplier admissible (gauge grade) field)
        (apMultiplier_identity_high admissible large field))
    exact (congrArg (apComplement L sigma gamma ell grade) multiplied).trans
      ((map_add (apComplement L sigma gamma ell grade) field (apMultiplier admissible (gauge grade) field)).trans
        ((congrArg (fun value : apGrade L sigma gamma ell 3 grade => value +
          apComplement L sigma gamma ell grade (apMultiplier admissible (gauge grade) field)) circular).trans (zero_add _)))
  exact (congrArg norm identity).trans_le ((apComplement_bound L sigma gamma ell grade _).trans
    ((mul_le_mul_of_nonneg_left (apMultiplier_bound admissible (gauge grade) field)
      (apComplementConstant_nonnegative grade)).trans_eq (mul_assoc _ _ _).symm))

end Grad.GaugeCoefficients.Physical.Compensated
