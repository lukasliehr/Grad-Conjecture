import AFX6ActualMatchingConsumer
import Mathlib.Analysis.Normed.Lp.ProdLp

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GenericCarriers Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The literal closed Q-range on the original full-cell AP3 coordinates. -/
def highBoundarySubmodule (L sigma gamma ell : ℝ) (grade : ℕ) :
    Submodule ℂ (APBoundaryGrade L sigma gamma ell 1 grade) :=
  (ContinuousLinearMap.id ℂ (APBoundaryGrade L sigma gamma ell 1 grade) -
    apHighProjection L sigma gamma ell grade).ker

abbrev HighBoundaryGrade (L sigma gamma ell : ℝ) (grade : ℕ) :=
  ↥(highBoundarySubmodule L sigma gamma ell grade)

instance highBoundaryComplete (L sigma gamma ell : ℝ) (grade : ℕ) :
    CompleteSpace (HighBoundaryGrade L sigma gamma ell grade) := by
  let : IsClosed (highBoundarySubmodule L sigma gamma ell grade : Set (APBoundaryGrade L sigma gamma ell 1 grade)) :=
    (ContinuousLinearMap.id ℂ (APBoundaryGrade L sigma gamma ell 1 grade) -
      apHighProjection L sigma gamma ell grade).isClosed_ker
  exact IsClosed.completeSpace_coe

theorem highBoundary_mem (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 grade) :
    field ∈ highBoundarySubmodule L sigma gamma ell grade ↔
      apHighProjection L sigma gamma ell grade field = field := by
  change field - apHighProjection L sigma gamma ell grade field = 0 ↔ _
  exact sub_eq_zero.trans eq_comm

theorem highBoundary_low (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : HighBoundaryGrade L sigma gamma ell grade) (mode : ℤ × ℤ)
    (low : ¬3 ≤ |mode.1|) : field.val mode = 0 := by
  have fixed := (highBoundary_mem L sigma gamma ell grade field.val).mp field.property
  have point := congrArg (fun v : APBoundaryGrade L sigma gamma ell 1 grade => v mode) fixed
  rw [apHighProjection_apply, if_neg low] at point
  exact point.symm

def highBoundaryProjection (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell 1 grade →L[ℂ] HighBoundaryGrade L sigma gamma ell grade :=
  (apHighProjection L sigma gamma ell grade).codRestrict
    (highBoundarySubmodule L sigma gamma ell grade) (fun field =>
      (highBoundary_mem L sigma gamma ell grade _).mpr
        (apHighProjection_idempotent L sigma gamma ell grade field))

theorem highBoundaryProjection_val (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 grade) :
    (highBoundaryProjection L sigma gamma ell grade field).val =
      apHighProjection L sigma gamma ell grade field := rfl

theorem highBoundaryProjection_bound (L sigma gamma ell : ℝ) (grade : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 grade) :
    ‖highBoundaryProjection L sigma gamma ell grade field‖ ≤ ‖field‖ :=
  apHighProjection_bound L sigma gamma ell grade field

/-- Weighted coordinates of C^(q-1/2). Its coefficient convention below,
not an extra tangential estimate, supplies the sigma/|m| weight. -/
abbrev StrongMatchingGrade (L sigma gamma ell : ℝ) (q : ℕ) :=
  HighBoundaryGrade L sigma gamma ell (q + 1)

def strongMatchingWeight (L sigma gamma ell : ℝ) (q : ℕ) (mode : ℤ × ℤ) : ℝ :=
  if 3 ≤ |mode.1| then apBoundaryWeight L sigma gamma ell (q + 1) mode / |(mode.1 : ℝ)| else 1

theorem highAngularAbs_pos (mode : ℤ × ℤ) (high : 3 ≤ |mode.1|) : 0 < |(mode.1 : ℝ)| := by
  have bound : (3 : ℝ) ≤ |(mode.1 : ℝ)| := by exact_mod_cast high
  linarith

theorem strongMatchingWeight_pos (L sigma gamma ell : ℝ) (q : ℕ) (mode : ℤ × ℤ) :
    0 < strongMatchingWeight L sigma gamma ell q mode := by
  unfold strongMatchingWeight
  split_ifs with high
  · exact div_pos (apBoundaryWeight_pos L sigma gamma ell (q + 1) mode) (highAngularAbs_pos mode high)
  · exact zero_lt_one

def strongMatchingCoefficient (L sigma gamma ell : ℝ) (q : ℕ)
    (field : StrongMatchingGrade L sigma gamma ell q) (mode : ℤ × ℤ) : PhysicalValue 1 :=
  ((strongMatchingWeight L sigma gamma ell q mode : ℂ)⁻¹) • field.val mode

theorem strongMatching_weighted_coefficient (L sigma gamma ell : ℝ) (q : ℕ)
    (field : StrongMatchingGrade L sigma gamma ell q) (mode : ℤ × ℤ) :
    (strongMatchingWeight L sigma gamma ell q mode : ℂ) •
      strongMatchingCoefficient L sigma gamma ell q field mode = field.val mode :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (strongMatchingWeight_pos L sigma gamma ell q mode).ne') _

theorem strongMatchingCoefficient_low (L sigma gamma ell : ℝ) (q : ℕ)
    (field : StrongMatchingGrade L sigma gamma ell q) (mode : ℤ × ℤ) (low : ¬3 ≤ |mode.1|) :
    strongMatchingCoefficient L sigma gamma ell q field mode = 0 := by
  unfold strongMatchingCoefficient
  rw [highBoundary_low L sigma gamma ell (q + 1) field mode low, smul_zero]

theorem strongMatchingWeight_sq (L sigma gamma ell : ℝ) (q : ℕ) (mode : ℤ × ℤ)
    (high : 3 ≤ |mode.1|) :
    strongMatchingWeight L sigma gamma ell q mode ^ 2 =
      Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) *
        apBoundaryFrequency L ell mode ^ (2 * q + 1) / (mode.1 : ℝ) ^ 2 := by
  have exponent : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  have exponential : Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) =
      Real.exp (apBoundaryPhase sigma gamma ell mode.2) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [strongMatchingWeight, if_pos high, div_pow, sq_abs, apBoundaryWeight, mul_pow,
    Real.sq_sqrt (pow_nonneg (apBoundaryFrequency_pos L ell mode).le _), exponent, exponential]

/-- AY1's exact original full-cell weighted norm, at all required half grades. -/
theorem strongMatching_norm_sq (L sigma gamma ell : ℝ) (q : ℕ)
    (field : StrongMatchingGrade L sigma gamma ell q) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      if 3 ≤ |mode.1| then
        Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) *
          apBoundaryFrequency L ell mode ^ (2 * q + 1) / (mode.1 : ℝ) ^ 2 *
            ‖strongMatchingCoefficient L sigma gamma ell q field mode‖ ^ 2
      else 0 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field.val
  norm_num at normFormula
  change ‖field.val‖ ^ 2 = _
  rw [normFormula]
  congr 1
  funext mode
  split_ifs with high
  · rw [← strongMatching_weighted_coefficient L sigma gamma ell q field mode, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (strongMatchingWeight_pos L sigma gamma ell q mode),
      mul_pow, strongMatchingWeight_sq L sigma gamma ell q mode high]
  · rw [highBoundary_low L sigma gamma ell (q + 1) field mode high, norm_zero, zero_pow (by decide)]

end Grad.GaugeCoefficients.Physical.Compensated
