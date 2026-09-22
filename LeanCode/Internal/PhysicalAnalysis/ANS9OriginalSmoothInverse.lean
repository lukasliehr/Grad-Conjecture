import ANS8NativeInverseBound

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra

/-- Literal cellwise jets remain in every original AP grade, with no change
of phase, scale, or analytic width. -/
theorem shiftInverse_summable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (grade : ℕ) (field : APSmooth L sigma gamma ell dimension) :
    Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell
      (shiftInverseJet shift (apSmoothJet admissible dimension cell field))) 2 := by
  let majorant : APAmbient dimension grade := (angularInverseConstant grade : ℂ) •
    (apSmoothGrade L sigma gamma ell dimension grade field).val
  apply (lp.memℓp majorant).mono'
  intro cell
  change ‖apRowLinear (grade := grade) L sigma gamma ell cell
    (shiftInverseJet shift (apSmoothJet admissible dimension cell field))‖ ≤
      ‖(angularInverseConstant grade : ℂ) • (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖
  have estimate := shiftInverse_row_bound (grade := grade) L sigma gamma ell cell shift (apSmoothJet admissible dimension cell field)
  have inputNorm := congrArg norm (apSmoothJet_row admissible field grade cell)
  have scaled : ‖(angularInverseConstant grade : ℂ) •
      (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ =
      angularInverseConstant grade * ‖(apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (angularInverseConstant_nonnegative grade)]
  exact estimate.trans_eq ((congrArg (fun value : ℝ => angularInverseConstant grade * value) inputNorm).trans scaled.symm)

theorem literalSmooth_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (fields : ℤ → ClosedJet dimension)
    (summable : ∀ grade : ℕ, Memℓp (fun cell => apRowLinear (grade := grade) L sigma gamma ell cell (fields cell)) 2)
    (cell : ℤ) : apSmoothJet admissible dimension cell (apLiteralSmooth L sigma gamma ell fields summable) = fields cell := by
  apply closedJet_eq_of_value_eq
  apply closedValueL2_injective dimension
  exact (apSmoothJet_l2 admissible (apLiteralSmooth L sigma gamma ell fields summable) 0 cell).trans
    (apLiteralGrade_l2 L sigma gamma ell fields (summable 0) cell)

def apShiftInverse {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (field : APSmooth L sigma gamma ell dimension) : APSmooth L sigma gamma ell dimension :=
  apLiteralSmooth L sigma gamma ell
    (fun cell => shiftInverseJet shift (apSmoothJet admissible dimension cell field))
    (fun grade => shiftInverse_summable admissible shift grade field)

theorem apShiftInverse_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apShiftInverse admissible shift field) =
      shiftInverseJet shift (apSmoothJet admissible dimension cell field) :=
  literalSmooth_jet admissible _ _ cell

def apShiftInverseLinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (shift : ℤ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension where
  toFun := apShiftInverse admissible shift
  map_add' first second := by
    apply apSmoothJet_ext admissible
    intro cell
    let project := apSmoothJet admissible dimension cell
    exact (apShiftInverse_jet admissible shift (first + second) cell).trans
      ((congrArg (shiftInverseJet shift) (project.map_add first second)).trans
        ((map_add (shiftInverseLinear dimension shift) (project first) (project second)).trans
          ((congrArg₂ (fun a b : ClosedJet dimension => a + b)
            (apShiftInverse_jet admissible shift first cell).symm
            (apShiftInverse_jet admissible shift second cell).symm).trans
              (project.map_add (apShiftInverse admissible shift first)
                (apShiftInverse admissible shift second)).symm)))
  map_smul' scalar field := by
    apply apSmoothJet_ext admissible
    intro cell
    let project := apSmoothJet admissible dimension cell
    exact (apShiftInverse_jet admissible shift (scalar • field) cell).trans
      ((congrArg (shiftInverseJet shift) (project.map_smul scalar field)).trans
        ((map_smul (shiftInverseLinear dimension shift) scalar (project field)).trans
          ((congrArg (fun value : ClosedJet dimension => scalar • value)
            (apShiftInverse_jet admissible shift field cell).symm).trans
              (project.map_smul scalar (apShiftInverse admissible shift field)).symm)))

theorem apShiftInverse_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (shift : ℤ) (grade : ℕ) (field : APSmooth L sigma gamma ell dimension) :
    ‖apSmoothGrade L sigma gamma ell dimension grade (apShiftInverse admissible shift field)‖ ≤
      angularInverseConstant grade * ‖apSmoothGrade L sigma gamma ell dimension grade field‖ := by
  change ‖(apSmoothGrade L sigma gamma ell dimension grade (apShiftInverse admissible shift field)).val‖ ≤ _
  calc
    _ ≤ ‖(angularInverseConstant grade : ℂ) •
        (apSmoothGrade L sigma gamma ell dimension grade field).val‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      change ‖(apSmoothGrade L sigma gamma ell dimension grade (apShiftInverse admissible shift field)).val cell‖ ≤
        ‖(angularInverseConstant grade : ℂ) • (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖
      have outputNorm := congrArg norm (apSmoothJet_row admissible (apShiftInverse admissible shift field) grade cell)
      have outputJet := congrArg (fun jet : ClosedJet dimension => ‖apRowLinear (grade := grade) L sigma gamma ell cell jet‖)
        (apShiftInverse_jet admissible shift field cell)
      have estimate := shiftInverse_row_bound (grade := grade) L sigma gamma ell cell shift (apSmoothJet admissible dimension cell field)
      have inputNorm := congrArg norm (apSmoothJet_row admissible field grade cell)
      have scaled : ‖(angularInverseConstant grade : ℂ) •
          (apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ =
          angularInverseConstant grade * ‖(apSmoothGrade L sigma gamma ell dimension grade field).val cell‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (angularInverseConstant_nonnegative grade)]
      exact (outputNorm.symm.trans outputJet).le.trans (estimate.trans_eq
        ((congrArg (fun value : ℝ => angularInverseConstant grade * value) inputNorm).trans scaled.symm))
    _ = _ := by
      have coefficient : ‖(angularInverseConstant grade : ℂ)‖ = angularInverseConstant grade :=
        (Complex.norm_real _).trans (Real.norm_of_nonneg (angularInverseConstant_nonnegative grade))
      exact (norm_smul (angularInverseConstant grade : ℂ)
        (apSmoothGrade L sigma gamma ell dimension grade field).val).trans
          (congrArg (fun value : ℝ => value * ‖apSmoothGrade L sigma gamma ell dimension grade field‖) coefficient)

end Grad.ActualAngularInverse
