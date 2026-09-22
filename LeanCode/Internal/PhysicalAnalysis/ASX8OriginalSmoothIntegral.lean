import ASX7OriginalPowerBound

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.ActualCenterVolterra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra

theorem originalPowerRowConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) : 0 ≤ originalPowerRowConstant L gamma grade :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg
    (fun _ _ => originalDilationWordConstant_nonnegative admissible _))

/-- Literal cellwise jets remain in every original AP grade, with no change
of phase, scale, or analytic width. -/
theorem originalPower_summable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (power grade : ℕ) (field : APSmooth L sigma gamma ell dimension) :
    Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell
      (powerDilationJet (power + 1) (apSmoothJet admissible dimension cell field))) 2 := by
  let majorant : APAmbient dimension grade := (originalPowerRowConstant L gamma grade : ℂ) •
    (apSmoothGrade L sigma gamma ell dimension grade field).val
  apply (lp.memℓp majorant).mono'
  intro cell
  change ‖apRowLinear (grade := grade) L sigma gamma ell cell
    (powerDilationJet (power + 1) (apSmoothJet admissible dimension cell field))‖ ≤
      ‖(originalPowerRowConstant L gamma grade : ℂ) • (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖
  have estimate := originalPowerRow_bound (grade := grade) admissible cell power (apSmoothJet admissible dimension cell field)
  have inputNorm := congrArg norm (apSmoothJet_row admissible field grade cell)
  have scaled : ‖(originalPowerRowConstant L gamma grade : ℂ) •
      (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ =
      originalPowerRowConstant L gamma grade * ‖(apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (originalPowerRowConstant_nonnegative admissible grade)]
  exact estimate.trans_eq ((congrArg (fun value : ℝ => originalPowerRowConstant L gamma grade * value) inputNorm).trans scaled.symm)

theorem literalSmooth_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (fields : ℤ → ClosedJet dimension)
    (summable : ∀ grade : ℕ, Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell)) 2)
    (cell : ℤ) : apSmoothJet admissible dimension cell (apLiteralSmooth L sigma gamma ell fields summable) = fields cell := by
  apply closedJet_eq_of_value_eq
  apply closedValueL2_injective dimension
  exact (apSmoothJet_l2 admissible (apLiteralSmooth L sigma gamma ell fields summable) 0 cell).trans
    (apLiteralGrade_l2 L sigma gamma ell fields (summable 0) cell)

def originalPowerSmooth {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (power : ℕ) (field : APSmooth L sigma gamma ell dimension) : APSmooth L sigma gamma ell dimension :=
  apLiteralSmooth L sigma gamma ell
    (fun cell => powerDilationJet (power + 1) (apSmoothJet admissible dimension cell field))
    (fun grade => originalPower_summable admissible power grade field)

theorem originalPowerSmooth_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (power : ℕ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (originalPowerSmooth admissible power field) =
      powerDilationJet (power + 1) (apSmoothJet admissible dimension cell field) :=
  literalSmooth_jet admissible _ _ cell

def originalPowerSmoothLinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension power : ℕ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension where
  toFun := originalPowerSmooth admissible power
  map_add' first second := by
    apply apSmoothJet_ext admissible
    intro cell
    let project := apSmoothJet admissible dimension cell
    exact (originalPowerSmooth_jet admissible power (first + second) cell).trans
      ((congrArg (powerDilationJet (power + 1)) (project.map_add first second)).trans
        ((powerDilationJet_add (power + 1) (project first) (project second)).trans
          ((congrArg₂ (fun a b : ClosedJet dimension => a + b)
            (originalPowerSmooth_jet admissible power first cell).symm
            (originalPowerSmooth_jet admissible power second cell).symm).trans
              (project.map_add (originalPowerSmooth admissible power first)
                (originalPowerSmooth admissible power second)).symm)))
  map_smul' scalar field := by
    apply apSmoothJet_ext admissible
    intro cell
    let project := apSmoothJet admissible dimension cell
    exact (originalPowerSmooth_jet admissible power (scalar • field) cell).trans
      ((congrArg (powerDilationJet (power + 1)) (project.map_smul scalar field)).trans
        ((powerDilationJet_smul (power + 1) scalar (project field)).trans
          ((congrArg (fun value : ClosedJet dimension => scalar • value)
            (originalPowerSmooth_jet admissible power field cell).symm).trans
              (project.map_smul scalar (originalPowerSmooth admissible power field)).symm)))

theorem originalPowerSmooth_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (power grade : ℕ) (field : APSmooth L sigma gamma ell dimension) :
    ‖apSmoothGrade L sigma gamma ell dimension grade (originalPowerSmooth admissible power field)‖ ≤
      originalPowerRowConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell dimension grade field‖ := by
  change ‖(apSmoothGrade L sigma gamma ell dimension grade (originalPowerSmooth admissible power field)).val‖ ≤ _
  calc
    _ ≤ ‖(originalPowerRowConstant L gamma grade : ℂ) •
        (apSmoothGrade L sigma gamma ell dimension grade field).val‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      change ‖(apSmoothGrade L sigma gamma ell dimension grade (originalPowerSmooth admissible power field)).val cell‖ ≤
        ‖(originalPowerRowConstant L gamma grade : ℂ) • (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖
      have outputNorm := congrArg norm (apSmoothJet_row admissible (originalPowerSmooth admissible power field) grade cell)
      have outputJet := congrArg (fun jet : ClosedJet dimension => ‖apRowLinear (grade := grade) L sigma gamma ell cell jet‖)
        (originalPowerSmooth_jet admissible power field cell)
      have estimate := originalPowerRow_bound (grade := grade) admissible cell power (apSmoothJet admissible dimension cell field)
      have inputNorm := congrArg norm (apSmoothJet_row admissible field grade cell)
      have scaled : ‖(originalPowerRowConstant L gamma grade : ℂ) •
          (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ =
          originalPowerRowConstant L gamma grade * ‖(apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (originalPowerRowConstant_nonnegative admissible grade)]
      exact (outputNorm.symm.trans outputJet).le.trans (estimate.trans_eq
        ((congrArg (fun value : ℝ => originalPowerRowConstant L gamma grade * value) inputNorm).trans scaled.symm))
    _ = _ := by
      have coefficient : ‖(originalPowerRowConstant L gamma grade : ℂ)‖ = originalPowerRowConstant L gamma grade :=
        (Complex.norm_real _).trans (Real.norm_of_nonneg (originalPowerRowConstant_nonnegative admissible grade))
      exact (norm_smul (originalPowerRowConstant L gamma grade : ℂ)
        (apSmoothGrade L sigma gamma ell dimension grade field).val).trans
          (congrArg (fun value : ℝ => value * ‖apSmoothGrade L sigma gamma ell dimension grade field‖) coefficient)

end Grad.ActualExceptionalInverse
