import AEN9ActualSharpPrimitiveBounds

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualExceptionalInverse Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

private theorem lp_norm_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] (source : lp (fun _ : ℤ => E) 2) (target : lp (fun _ : ℤ => F) 2)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (bounded : ∀ cell, ‖target cell‖ ≤ constant * ‖source cell‖) :
    ‖target‖ ≤ constant * ‖source‖ := by
  calc
    _ ≤ ‖(constant : ℂ) • source‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      change ‖target cell‖ ≤ ‖(constant : ℂ) • source cell‖
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]
      exact bounded cell
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative]

/-- One literal original-row bound synthesizes directly into the completed
original AP norm, allowing distinct source and target grades. -/
theorem smoothNorm_of_cellBounds (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (source : APSmooth L sigma gamma ell input) (target : APSmooth L sigma gamma ell output)
    (sourceGrade targetGrade : ℕ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell, ‖apRowLinear (grade := targetGrade) L sigma gamma ell cell (apSmoothJet admissible output cell target)‖ ≤
      constant * ‖apRowLinear (grade := sourceGrade) L sigma gamma ell cell (apSmoothJet admissible input cell source)‖) :
    ‖apSmoothGrade L sigma gamma ell output targetGrade target‖ ≤
      constant * ‖apSmoothGrade L sigma gamma ell input sourceGrade source‖ := by
  apply lp_norm_bound (apSmoothGrade L sigma gamma ell input sourceGrade source).val
    (apSmoothGrade L sigma gamma ell output targetGrade target).val constant nonnegative
  intro cell
  have first := congrArg norm (apSmoothJet_row admissible target targetGrade cell)
  have second := congrArg norm (apSmoothJet_row admissible source sourceGrade cell)
  exact first.symm.le.trans ((bounded cell).trans_eq (congrArg (fun value : ℝ => constant * value) second))

def SmoothCellSupported (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (cells : ℤ → Prop) (field : APSmooth L sigma gamma ell dimension) : Prop :=
  ∀ cell, ¬cells cell → apSmoothJet admissible dimension cell field = 0

theorem smoothSupport_of_jetMap (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (cells : ℤ → Prop) (source : APSmooth L sigma gamma ell input) (target : APSmooth L sigma gamma ell output)
    (mapping : ℤ → ClosedJet input →ₗ[ℂ] ClosedJet output)
    (literal : ∀ cell, apSmoothJet admissible output cell target = mapping cell (apSmoothJet admissible input cell source))
    (supported : SmoothCellSupported admissible cells source) : SmoothCellSupported admissible cells target := by
  intro cell outside
  rw [literal, supported cell outside, map_zero]

theorem smoothSupport_add (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (cells : ℤ → Prop) (first second : APSmooth L sigma gamma ell dimension)
    (firstSupported : SmoothCellSupported admissible cells first) (secondSupported : SmoothCellSupported admissible cells second) :
    SmoothCellSupported admissible cells (first + second) := by
  intro cell outside
  rw [map_add, firstSupported cell outside, secondSupported cell outside, add_zero]

theorem smoothSupport_smul (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (cells : ℤ → Prop) (scalar : ℂ) (field : APSmooth L sigma gamma ell dimension)
    (supported : SmoothCellSupported admissible cells field) : SmoothCellSupported admissible cells (scalar • field) := by
  intro cell outside
  rw [map_smul, supported cell outside, smul_zero]

theorem smoothSupport_sub (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (cells : ℤ → Prop) (first second : APSmooth L sigma gamma ell dimension)
    (firstSupported : SmoothCellSupported admissible cells first) (secondSupported : SmoothCellSupported admissible cells second) :
    SmoothCellSupported admissible cells (first - second) := by
  intro cell outside
  rw [map_sub, firstSupported cell outside, secondSupported cell outside, sub_self]

def smoothSpinConstant : ℝ := max ‖spinValue (1 : ℂ)‖ ‖spinValue (-1 : ℂ)‖

theorem smoothSpinConstant_nonnegative : 0 ≤ smoothSpinConstant := (norm_nonneg _).trans (le_max_left _ _)

theorem smoothSpin_bound (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (smoothSpin L sigma gamma ell sign field)‖ ≤
      smoothSpinConstant * ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  have bound : ‖spinValue (sign : ℂ)‖ ≤ smoothSpinConstant := by
    unfold smoothSpinConstant
    rcases signed with rfl | rfl
    · simpa only [Int.cast_one] using (le_max_left ‖spinValue (1 : ℂ)‖ ‖spinValue (-1 : ℂ)‖)
    · simpa only [Int.cast_neg, Int.cast_one] using (le_max_right ‖spinValue (1 : ℂ)‖ ‖spinValue (-1 : ℂ)‖)
  exact (apSmoothValueMap_bound (spinValue (sign : ℂ)) field grade).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))

def smoothSignedDerivativeConstant (L gamma : ℝ) (grade : ℕ) : ℝ := smoothSpinConstant * gradientBoundConstant L gamma grade

theorem smoothSignedDerivativeConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ smoothSignedDerivativeConstant L gamma grade :=
  mul_nonneg smoothSpinConstant_nonnegative (gradientBoundConstant_nonnegative admissible grade)

theorem smoothSignedDerivative_bound (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell 1) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (smoothSignedDerivative admissible 1 sign field)‖ ≤
      smoothSignedDerivativeConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖ := by
  have literal := smoothSpin_gradient admissible (-sign) field
  rw [neg_neg] at literal
  have spin := smoothSpin_bound (-sign) (by rcases signed with rfl | rfl <;> norm_num)
    (apSmoothGradient admissible field) grade
  have gradient := mul_le_mul_of_nonneg_left (apSmoothGradient_bound admissible field grade) smoothSpinConstant_nonnegative
  exact (congrArg (fun value => ‖apSmoothGrade L sigma gamma ell 1 grade value‖) literal).symm.le.trans
    ((spin.trans gradient).trans_eq (mul_assoc _ _ _).symm)

theorem signedHalfInverse_norm (sign : ℤ) (signed : sign = 1 ∨ sign = -1) :
    ‖(2 * Complex.I * (sign : ℂ))⁻¹‖ ≤ 1 := by rcases signed with rfl | rfl <;> norm_num

theorem signedQuarterInverse_norm (sign : ℤ) (signed : sign = 1 ∨ sign = -1) :
    ‖(4 * Complex.I * (sign : ℂ))⁻¹‖ ≤ 1 := by rcases signed with rfl | rfl <;> norm_num

end Grad.ExceptionalNative
