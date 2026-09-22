import ACF1SameCellProductRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.SameCellFixedMultiplication
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- The existing actual fixed multiplier has a same-grade bound with its
constant chosen before sigma, ell and the input, on all original cells. -/
theorem apSmoothFixedJet_uniform_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (coefficient : SmoothOperatorJet input output)
    (field : APSmooth L sigma gamma ell input) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell output grade (apSmoothFixedJet admissible coefficient field)‖ ≤
      fixedRowConstant grade coefficient * ‖apSmoothGrade L sigma gamma ell input grade field‖ := by
  change ‖(apSmoothGrade L sigma gamma ell output grade (apSmoothFixedJet admissible coefficient field)).val‖ ≤ _
  calc
    _ ≤ ‖(fixedRowConstant grade coefficient : ℂ) • (apSmoothGrade L sigma gamma ell input grade field).val‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      change ‖(apSmoothGrade L sigma gamma ell output grade (apSmoothFixedJet admissible coefficient field)).val cell‖ ≤
        ‖(fixedRowConstant grade coefficient : ℂ) • (apSmoothGrade L sigma gamma ell input grade field).val cell‖
      have outputNorm := congrArg norm (apSmoothJet_row admissible (apSmoothFixedJet admissible coefficient field) grade cell)
      have outputJet := congrArg (fun jet : ClosedJet output => ‖apRowLinear (grade := grade) L sigma gamma ell cell jet‖)
        (apSmoothFixedJet_jet admissible coefficient field cell)
      have estimate := fixedProduct_row_bound (grade := grade) L sigma gamma ell cell coefficient (apSmoothJet admissible input cell field)
      have inputNorm := congrArg norm (apSmoothJet_row admissible field grade cell)
      have scaled : ‖(fixedRowConstant grade coefficient : ℂ) •
          (apSmoothGrade L sigma gamma ell input grade field).val cell‖ =
          fixedRowConstant grade coefficient * ‖(apSmoothGrade L sigma gamma ell input grade field).val cell‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (fixedRowConstant_nonnegative grade coefficient)]
      exact (outputNorm.symm.trans outputJet).le.trans (estimate.trans_eq
        ((congrArg (fun value : ℝ => fixedRowConstant grade coefficient * value) inputNorm).trans scaled.symm))
    _ = _ := by
      have coefficientNorm : ‖(fixedRowConstant grade coefficient : ℂ)‖ = fixedRowConstant grade coefficient :=
        (Complex.norm_real _).trans (Real.norm_of_nonneg (fixedRowConstant_nonnegative grade coefficient))
      exact (norm_smul (fixedRowConstant grade coefficient : ℂ) (apSmoothGrade L sigma gamma ell input grade field).val).trans
        (congrArg (fun value : ℝ => value * ‖apSmoothGrade L sigma gamma ell input grade field‖) coefficientNorm)

end Grad.SameCellFixedMultiplication
